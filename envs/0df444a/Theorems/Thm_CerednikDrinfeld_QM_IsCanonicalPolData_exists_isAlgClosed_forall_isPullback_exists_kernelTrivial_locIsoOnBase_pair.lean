-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCanonicalPolData_exists_isAlgClosed_forall_isPullback_exists_kernelTrivial_locIsoOnBase_pair
-- name    : CerednikDrinfeld.QM.IsCanonicalPolData.exists_isAlgClosed_forall_isPullback_exists_kernelTrivial_locIsoOnBase_pair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/3ef7e5d8-adac-5fbf-b7a8-65c1818efa28
-- title:
--   Simultaneous principal square roots over an algebraically closed extension
-- statement:
--   Let $k$ be a field, let $f : A \to \operatorname{Spec} k$ be a scheme over $k$ equipped with a relative group law $L$ (functorial multiplication, unit and inverse on sections of $f$ over varying $k$-bases, with the group axioms and compatibility with base change), let $I$ be a type, $\mathrm{act} : I \to (A \to A)$ a family of endomorphisms of $A$ with $\mathrm{act}\,x$ followed by $f$ equal to $f$ for every $x$, and let $\star : I \to I$. Suppose two objects $\mathcal L, \mathcal M$ of $A$-modules each satisfy `IsCanonicalPolData` for these data, i.e. each is invertible (locally on $A$ isomorphic to the unit), symmetric in the sense that its pullback along the inversion morphism $\mathrm{negMor}$ is isomorphic to it locally over the base, satisfies the predicate `KernelIsTwoTorsion` for $(f,L)$, admits — after base change to some faithfully flat $k$-algebra $S'$ — a principal square root for every relative group law on the pulled-back family compatible with $L$ via the first projection, has positive `geomFibreH0Finrank` on every geometric fibre over an algebraically closed field, and is `RosatiCompatible` with $\mathrm{act}$ and $\star$. Then there exist a type $k''$ carrying a field structure, an algebraic closedness instance and a $k$-algebra structure, such that for every scheme $A''$, every $f'' : A'' \to \operatorname{Spec} k''$, every $g : A'' \to A$ making the square with $f''$, $f$ and $\operatorname{Spec}$ of $k \to k''$ cartesian, and every relative group law $L''$ on $f''$ for which $g$ is multiplicative (for all $t' : T \to \operatorname{Spec} k''$ and sections $P,Q$ of $f''$ over $t'$, the underlying morphism of $L''.\mathrm{mul}\,t'\,P\,Q$ followed by $g$ equals that of $L.\mathrm{mul}$ applied to $P$ and $Q$ composed with $g$ over $t'$ followed by $\operatorname{Spec}(k \to k'')$), the following holds for both $\mathcal L$ and $\mathcal M$: there is an invertible $\mathcal L_1$ on $A''$ with `KernelTrivial` for $(f'', L'')$ — any section $x$ of $f''$ over any $\operatorname{Spec} R \to \operatorname{Spec} k''$ whose slice of the Mumford bundle of $\mathcal L_1$ is locally on the base trivial equals the unit section — such that $g^{*}\mathcal L$ and $\mathcal L_1 \otimes \mathrm{negMor}(f'',L'')^{*}\mathcal L_1$ become isomorphic over the preimages of a neighbourhood of each point of $\operatorname{Spec} k''$; similarly for $\mathcal M$ with some invertible $\mathcal M_1$.
--
--   This is the step extracting from two canonical polarisation data a single algebraically closed extension of the base field over which both data simultaneously acquire principal square roots, on every cartesian base change and for every compatible group law there. It is used in the comparison of canonical polarisations on fake elliptic curves, by [`CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isAlgClosed`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.locIsoOnBase_of_isCanonicalPol_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCanonicalPolData_exists_isAlgClosed_forall_isPullback_exists_kernelTrivial_locIsoOnBase_pair.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.IsCanonicalPolData.exists_isAlgClosed_forall_isPullback_exists_kernelTrivial_locIsoOnBase_pair
    (k : Type) [Field k] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I)
    (𝓛 𝓜 : A.Modules) (h𝓛 : IsCanonicalPolData f L act act_over star 𝓛) (h𝓜 : IsCanonicalPolData f L act act_over star 𝓜) :
    ∃ (k'' : Type) (_ : Field k'') (_ : IsAlgClosed k'') (_ : Algebra k k''),
      ∀ {A'' : Scheme} (f'' : A'' ⟶ Spec (CommRingCat.of k'')) (g : A'' ⟶ A)
        (hg : IsPullback g f'' f (Spec.map (CommRingCat.ofHom (algebraMap k k''))))
        (L'' : RelativeGroupLaw k'' f''),
        (∀ {T : Scheme} (t' : T ⟶ Spec (CommRingCat.of k'')) (P Q : SchemeHomOver t' f''),
            (L''.mul t' P Q).1 ≫ g =
              (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'')))
                ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) →
        (∃ 𝓛₁ : A''.Modules, Scheme.Modules.IsInvertible 𝓛₁ ∧ KernelTrivial f'' L'' 𝓛₁ ∧
            LocIsoOnBase f'' ((Scheme.Modules.pullback g).obj 𝓛) (𝓛₁ ⊗ (Scheme.Modules.pullback (negMor f'' L'')).obj 𝓛₁)) ∧
        (∃ 𝓜₁ : A''.Modules, Scheme.Modules.IsInvertible 𝓜₁ ∧ KernelTrivial f'' L'' 𝓜₁ ∧
            LocIsoOnBase f'' ((Scheme.Modules.pullback g).obj 𝓜) (𝓜₁ ⊗ (Scheme.Modules.pullback (negMor f'' L'')).obj 𝓜₁)) := by sorry
