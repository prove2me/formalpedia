-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_closedImmersion_proj_of_twisted_affine_chart_ratios
-- name    : AlgebraicGeometry.exists_closedImmersion_proj_of_twisted_affine_chart_ratios
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-07T20:46:53.92871+00:00
-- url     : https://prove2.me/theorems/99f67118-7dbe-4f27-afc4-b15ddcfc0fa0
-- title:
--   Projective embeddings from twisted affine chart ratios
-- statement:
--   Let $R$ be a commutative ring and let $\pi:X\to\operatorname{Spec}R$ be proper, with $X$ integral. Suppose that finitely many affine opens $V_i$ cover $X$, and choose opens $O_i\supseteq V_i$.
--
--   For each pair, suppose that there are functions $b_{ij}\in\Gamma(V_i,\mathcal O_X)$ and $a_{ij}\in\Gamma(V_i\cap O_j,\mathcal O_X)$ satisfying
--   $$D(b_{ij})=V_i\cap O_j,\qquad D(a_{ij})=V_i\cap V_j.$$
--   Assume the identity relations $b_{ii}=1$ and $a_{ii}=1$, and the multiplicative compatibility relations
--   $$b_{ik}=b_{ij}b_{jk}\quad\text{on }V_i\cap V_j,$$
--   $$a_{ik}=a_{ij}a_{jk}\quad\text{on }V_i\cap V_j\cap O_k.$$
--   Every equality uses the restrictions from its stated original domain.
--
--   Then, for some finite $n$, the same scheme $X$ admits a closed immersion $j:X\hookrightarrow\mathbb P^n_R$ whose composite with the projective-space projection is exactly $\pi$.
--
--   The functions $a_{ij}$ need not extend to all of $V_i$. The proof constructs one common power of the $b_{ij}$ that clears these denominators while preserving the exact basic opens, derives a cocycle on the affine charts, and constructs projective coordinates. Empty members of the finite cover are permitted. No Noetherian assumption on $R$ is required.
-- source:
--   Derived integral finite-chart form of the denominator-clearing and twisting argument in the Stacks Project, Lemma 28.18.2 (tag 01PW), https://stacks.math.columbia.edu/tag/01PW , and the proof of Lemma 29.38.7(1), https://stacks.math.columbia.edu/tag/01VG . This statement exposes the local functions and their exact nonvanishing loci instead of assuming a global ample sheaf. Its integral hypothesis is explicit. The projective-coordinate construction uses the public Proved native presentation theorem https://prove2.me/theorems/e1f5bbdc-0754-5d5b-904d-1c5a989b084c . The Philippon alteration development applies this criterion to the same actual glued nodal Cartier modification over a projective base; the full alteration theorem is a separate remaining step.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
universe u

theorem AlgebraicGeometry.exists_closedImmersion_proj_of_twisted_affine_chart_ratios {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (CommRingCat.of R)) [IsProper π]
    {r : ℕ} (V O : Fin r → X.Opens) (hVO : ∀ i, V i ≤ O i)
    (hAffine : ∀ i, IsAffineOpen (V i)) (hCover : iSup V = ⊤)
    (b : ∀ i j, Γ(X, V i)) (hbself : ∀ i, b i i = 1)
    (hbopen : ∀ i j, X.basicOpen (b i j) = V i ⊓ O j)
    (hbmul : ∀ i j k,
      X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (b i k) =
        X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (b i j) *
          X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (b j k))
    (a : ∀ i j, Γ(X, V i ⊓ O j))
    (haself : ∀ i, a i i = X.presheaf.map (homOfLE (inf_le_left : V i ⊓ O i ≤ V i)).op 1)
    (haopen : ∀ i j, X.basicOpen (a i j) = V i ⊓ V j)
    (hamul : ∀ i j k,
      X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
        (V i ⊓ V j) ⊓ O k ≤ V i ⊓ O k)).op (a i k) =
        X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left)
          ((inf_le_left.trans inf_le_right).trans (hVO j)) :
          (V i ⊓ V j) ⊓ O k ≤ V i ⊓ O j)).op (a i j) *
        X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          (V i ⊓ V j) ⊓ O k ≤ V j ⊓ O k)).op (a j k)) :
    ∃ (n : ℕ) (j : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)),
      IsClosedImmersion j ∧ j ≫ ProjSpace.π R n = π := by sorry
