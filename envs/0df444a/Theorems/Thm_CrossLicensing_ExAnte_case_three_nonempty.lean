-- Prove2me | Theorems.Thm_CrossLicensing_ExAnte_case_three_nonempty
-- name    : CrossLicensing.ExAnte.case_three_nonempty
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T14:39:40.144827+00:00
-- url     : https://prove2.me/theorems/8796a81b-9e4b-4111-ad34-2c5dbeeacc06
-- title:
--   Proof of Proposition 4(iii), p. A.3 — the third region exists iff k₁ > 7/12
-- statement:
--   Fix $k_1>49/144$. A superior-manufacturer cost in the third comparison region exists exactly when $k_1>7/12$:
--
--   $$\bigl(\exists k_2:\ 49/144<k_2<k_1,\ \hat k_2(k_1\mid0)\le k_2\bigr)\quad\Longleftrightarrow\quad \frac7{12}<k_1.$$
--
--   This determines when Proposition 4's interior-versus-interior comparison has any admissible cost coefficient.
-- source:
--   Wang, Huang, Lee, Cross-licensing in a Supply Chain with Asymmetric Manufacturers, SSRN 3053682 (version of 2023-04-27), p. A.3 (PDF 35), proof of Proposition 4(iii), opening sentence

import Definitions.Def_CrossLicensing_ExAnte_Model

namespace CrossLicensing.ExAnte

/-- Proof of Proposition 4(iii), p. A.3: the third cost region exists
precisely above the displayed threshold. -/
theorem case_three_nonempty (k1 : ℝ) (hk1 : (49 : ℝ) / 144 < k1) :
    (∃ k2 : ℝ, (49 : ℝ) / 144 < k2 ∧ khat2 k1 0 ≤ k2 ∧ k2 < k1) ↔
      (7 : ℝ) / 12 < k1 := by sorry

end CrossLicensing.ExAnte
