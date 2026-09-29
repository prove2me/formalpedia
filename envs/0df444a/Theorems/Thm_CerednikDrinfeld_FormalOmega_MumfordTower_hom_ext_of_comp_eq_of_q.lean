-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordTower_hom_ext_of_comp_eq_of_q
-- name    : CerednikDrinfeld.FormalOmega.MumfordTower.hom_ext_of_comp_eq_of_q
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/eaaf133b-31e7-59c7-b11f-2c365392085a
-- title:
--   Chart-local points are jointly epimorphic on a tower level
-- statement:
--   Let $\mathcal O$ be a commutative ring, $\pi \in \mathcal O$, $K_0$ a field that is an $\mathcal O$-algebra, $r$ a natural number, $g_1 \in \mathrm{GL}_2(K_0)$ and $N$ a subgroup of $\mathrm{PGL}_2(K_0)$, and let $D$ be a `MumfordTower` for these data: a family of schemes $D.Z\,m$ with structure morphisms $D.zb\,m : D.Z\,m \to \operatorname{Spec}(\mathcal O/(\pi^{m+1}))$ that are proper and flat, transition morphisms realising $D.Z\,m$ as the pullback of $D.Z\,(m+1)$, a finite-subset-to-affine-open property, and point maps $D.q\,m\,B\,h_B$ sending a Deligne datum over an $\mathcal O$-algebra $B$ with $(\pi)^{m+1} = 0$ in $B$ to a morphism $\operatorname{Spec} B \to D.Z\,m$, subject to compatibility over $\operatorname{Spec}(\mathcal O/(\pi^{m+1}))$, functoriality in $B$, compatibility with the transition morphisms, $N$-invariance and chart open-immersion axioms. Fix $n$, an $\mathcal O$-algebra $C$ in which $(\pi)^{n+1} = 0$, a scheme $X'$, morphisms $p_1 : X' \to D.Z\,n$, $p_2 : X' \to \operatorname{Spec} C$ and $s : \operatorname{Spec} C \to \operatorname{Spec}(\mathcal O/(\pi^{n+1}))$ such that $s$ followed by $\operatorname{Spec}$ of the quotient map $\mathcal O \to \mathcal O/(\pi^{n+1})$ is the structure morphism $\operatorname{Spec} C \to \operatorname{Spec}\mathcal O$, and such that $(p_1,p_2)$ exhibits $X'$ as the pullback of $D.zb\,n$ along $s$. Let $T$ be a scheme and $w, w' : X' \to T$ two morphisms such that for every $\mathcal O$-algebra $B$ with $(\pi)^{n+1} = 0$, every $\mathcal O$-algebra map $c : C \to B$, every Deligne datum $P$ over $B$ (an assignment, to each full lattice $M \subset K_0^2$, of a $B$-submodule of $B \otimes_{\mathcal O} M$ with invertible quotient, monotone in $M$, equivariant for scalar homotheties and non-degenerate at every prime of $B$) and every $x : \operatorname{Spec} B \to X'$ with $x$ followed by $p_1$ equal to $D.q\,n\,B\,h_B\,P$ and $x$ followed by $p_2$ equal to $\operatorname{Spec} c$, one has $x \gg w = x \gg w'$. Then $w = w'$.
--
--   This is the separatedness, or uniqueness, half of the representability statement for morphisms out of a base change of a level of the Mumford tower: the points coming from Deligne data over $\pi^{n+1}$-torsion $\mathcal O$-algebras, together with a compatible map to $\operatorname{Spec} C$, are jointly epimorphic on $X'$. It is used by [`CerednikDrinfeld.FormalOmega.MumfordTower.existsUnique_hom_pullback_of_natural_of_invariant`](thm.html#CerednikDrinfeld.FormalOmega.MumfordTower.existsUnique_hom_pullback_of_natural_of_invariant), where the existence half supplies the morphism and this result pins it down.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_MumfordTower_hom_ext_of_comp_eq_of_q.lean

import Definitions.Def_CerednikDrinfeld_MumfordTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.MumfordTower.hom_ext_of_comp_eq_of_q
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (r : ℕ)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (N : Subgroup (PGL(2, K₀)))
    (D : MumfordTower 𝒪 π K₀ r g₁ N) (n : ℕ)
    (C : Type) [CommRing C] [Algebra 𝒪 C] (hC : (algebraMap 𝒪 C π) ^ (n + 1) = 0)
    (X' : Scheme.{0}) (p₁ : X' ⟶ D.Z n) (p₂ : X' ⟶ Spec (CommRingCat.of C))
    (s : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (hs : s ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 C)))
    (hX' : IsPullback p₁ p₂ (D.zb n) s)
    (T : Scheme.{0})
    (w w' : X' ⟶ T)
    (h : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (c : C →ₐ[𝒪] B)
      (P : (Omega K₀ π).obj B) (x : Spec (CommRingCat.of B) ⟶ X'),
      x ≫ p₁ = D.q n B hB P → x ≫ p₂ = Spec.map (CommRingCat.ofHom c.toRingHom) → x ≫ w = x ≫ w') :
    w = w' := by sorry
