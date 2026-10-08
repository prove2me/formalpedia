-- Prove2me | Theorems.Thm_FeaturePricing_Ellipsoid_lemma2_rank_one_min_eigenvalue
-- name    : FeaturePricing.Ellipsoid.lemma2_rank_one_min_eigenvalue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:33:02.522413+00:00
-- url     : https://prove2.me/theorems/bb8efffb-bd5e-42fc-9527-c822e8786f34
-- title:
--   Lemma 2, p. 17 — z < λ_d(A) and φ_D(z) ≥ 0 imply σ_d ≥ z for D = A − βbb′
-- statement:
--   Let $A$ be a symmetric $d\times d$ real matrix ($d\ge1$) with eigenvalues $\lambda_1\ge\dots\ge\lambda_d$, let $b\in\mathbb R^d$, $\beta>0$, and let $D=A-\beta bb'$ have eigenvalues $\sigma_1\ge\dots\ge\sigma_d$. Write $\varphi_D(z)=\det(D-zI)$ for the characteristic polynomial of $D$ (with the paper's sign convention). For every $z<\lambda_d$,
--   $$
--   \varphi_D(z)\ge0\ \Longrightarrow\ \sigma_d\ge z.
--   $$
--
--   Lemma 2 is the tool that turns a sign check of the characteristic polynomial of a rank-one perturbation into a lower bound on its smallest eigenvalue; Lemmas 3 and 4 apply it to the update (4).
--
--   **Formalization Note** $\lambda_d$ and $\sigma_d$ are `lamMin A` and `lamMin D`, the minima of the real spectra. $\varphi_D(z)$ is $\det(D-zI)$ as printed in §5.4 (p. 16), not Mathlib's `charpoly`, which is $\det(zI-D)$ and differs by $(-1)^d$. Symmetry of $A$ and $\beta>0$ come from the standing context of §5.4 (p. 16); $d\ge1$ makes $\lambda_d$ exist.
-- source:
--   Cohen, Lobel, Paes Leme, Feature-Based Dynamic Pricing, Management Science (2020), DOI 10.1287/mnsc.2019.3485 (authors' copy, SSRN 2737045), p. 17, Lemma 2 (context §5.4, p. 16)

import Mathlib
import Definitions.Def_FeaturePricing_Ellipsoid_MinEigenvalue

namespace FeaturePricing.Ellipsoid

open Matrix

/-- **Lemma 2, p. 17** (with the standing context of §5.4, p. 16). Let `A` be a symmetric
`d × d` matrix (`d ≥ 1`), `b ∈ ℝ^d`, `β > 0`, and `D = A − βbb′`. If `z < λ_d(A)` and
`φ_D(z) = det(D − zI) ≥ 0`, then `σ_d = λ_d(D) ≥ z`. -/
theorem lemma2_rank_one_min_eigenvalue {d : ℕ} (hd : 0 < d) (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (b : Fin d → ℝ) (β : ℝ) (hβ : 0 < β) (z : ℝ) (hz : z < lamMin A)
    (hφ : 0 ≤ (A - β • vecMulVec b b - z • (1 : Matrix (Fin d) (Fin d) ℝ)).det) :
    z ≤ lamMin (A - β • vecMulVec b b) := by sorry

end FeaturePricing.Ellipsoid
