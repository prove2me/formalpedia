-- Prove2me | Theorems.Thm_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus
-- name    : AlgebraicGeometry.isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/3d39ba68-6980-54c3-a238-cde39634e6c2
-- title:
--   Finite m-torsion when a split torus has finite index
-- statement:
--   Let $k$ be an algebraically closed field, $X$ a scheme and $f : X \to \operatorname{Spec} k$ a quasi-compact morphism that is locally of finite type. Let $L$ be a relative group law on $f$ over $k$: a rule assigning to every test morphism $t : T \to \operatorname{Spec} k$ a multiplication, a unit and an inverse on the set $\{\varphi : T \to X \mid \varphi \text{ followed by } f = t\}$, satisfying associativity, both unit laws and left inverse, and natural in $T$ under precomposition; assume $L$ is commutative, i.e. all these multiplications are commutative. Let $t \in \mathbb{N}$ and let $\iota : \operatorname{Spec} k[\mathbb{Z}^t] \to X$, where $k[\mathbb{Z}^t]$ is the group algebra $\mathrm{AddMonoidAlgebra}\ k\ (\mathrm{Fin}\ t \to \mathbb{Z})$, be simultaneously an open immersion and a closed immersion, such that $\iota$ followed by $f$ is $\operatorname{Spec}$ of the structure map $k \to k[\mathbb{Z}^t]$, and such that for every $n \in \mathbb{N}$ the composite of $\iota$ with `L.schemeNsmul n` (the underlying morphism $X \to X$ of the $n$-th $L$-power of the identity point $\mathrm{id}_X$ in the group of points over $f$) equals $\operatorname{Spec}$ of the ring map induced by $n \cdot \mathrm{id}$ on $\mathrm{Fin}\ t \to \mathbb{Z}$, followed by $\iota$. Let $S$ be a finite set of sections of $f$ over $\operatorname{Spec} k$ such that every section $x$ of $f$ over $\operatorname{Spec} k$ can be written as the $L$-product of some $s \in S$ with $\tau$ followed by $\iota$, for some $k$-point $\tau$ of $\operatorname{Spec} k[\mathbb{Z}^t]$ over $\operatorname{Spec} k$. Then for every $m \in \mathbb{N}$ with $m > 0$, the structure morphism `L.schemeKerStr m` of the kernel $X[m]$, namely the second projection of the pullback of `L.schemeNsmul m` along the identity section $\operatorname{Spec} k \to X$, is a finite morphism, and the $k$-algebra $\Gamma(X[m], \top)$, with the $k$-algebra structure induced by that structure morphism, satisfies $\dim_k \Gamma(X[m], \top) \le |S| \cdot m^t$.
--
--   This is the statement that the $m$-torsion of a commutative group law whose identity component is a split torus of rank $t$ and of finite index on $k$-points is finite over $k$, with the explicit bound $|S| \cdot m^t$ on the dimension of its ring of global sections. It is applied in the analysis of the special fibre of the Néron model attached to $J_0$ at a prime, via [`ModularCurve.JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le`](thm.html#ModularCurve.JZeroNeronObjectAtP.isFinite_schemeKerStr_kerPairLaw_special_and_finrank_le); the proof uses density of the $k$-rational points of a scheme locally of finite type over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (L : RelativeGroupLaw k f) (hcomm : L.IsCommutative)
    (t : ℕ) (ι : Spec (CommRingCat.of (AddMonoidAlgebra k (Fin t → ℤ))) ⟶ X) [IsOpenImmersion ι] [IsClosedImmersion ι]
    (hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k (Fin t → ℤ)))))
    (hιn : ∀ n : ℕ, ι ≫ L.schemeNsmul n =
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainRingHom k (n • AddMonoidHom.id (Fin t → ℤ)))) ≫ ι)
    (S : Finset (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f))
    (hidx : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, ∃ s ∈ S,
      ∃ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k (Fin t → ℤ))))),
        x = L.mul (𝟙 _) s ⟨τ.1 ≫ ι, by rw [Category.assoc, hιf, τ.2]⟩)
    (m : ℕ) (hm : 0 < m) :
    IsFinite (L.schemeKerStr m) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom (L.schemeKerStr m) ⊤
     Module.finrank k Γ(L.schemeKer m, ⊤) ≤ S.card * m ^ t) := by sorry
