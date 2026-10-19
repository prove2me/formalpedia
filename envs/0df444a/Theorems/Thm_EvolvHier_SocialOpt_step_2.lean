-- Prove2me | Theorems.Thm_EvolvHier_SocialOpt_step_2
-- name    : EvolvHier.SocialOpt.step_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:17.794438+00:00
-- url     : https://prove2.me/theorems/f42a1370-a779-45d2-acfe-d48e1a74a1a1
-- title:
--   Step 2 — constant profile of equal length uses less investment
-- statement:
--   Suppose a nonnegative profile $x$ has finite expected length and its investments differ among agents with positive probability of being reached. Then there is a unique constant profile $y=(\gamma,\gamma,\ldots)$ of the same expected length, and it uses strictly less expected investment:
--
--   $$L(y)=L(x),\qquad I(y)<I(x).$$
--
--   This is the constant-profile comparison used in the optimality argument.
--
--   **Formalization Note** Nonconstancy is tested on realized support. The added finite-length condition and this reading exclude counterexamples in which all variation occurs after recruitment has stopped or the length is infinite.
-- source:
--   Hougaard, Moreno-Ternero & Østerdal, Optimal Management of Evolving Hierarchies, UPO WP ECON 21.15 (Aug. 3, 2021; Manag. Sci. doi:10.1287/mnsc.2021.4185), proof of Theorem 2, Step 2, pp. 24–25

import Mathlib
import Definitions.Def_EvolvHier_SocialOpt_Setting

namespace EvolvHier.SocialOpt

/-- Proof of Theorem 2, Step 2, with nonconstancy measured on realized agents. -/
theorem step_2 (T : Technology) (x : ℕ → ℝ)
    (hx : IsProfile x) (hL : L T x ≠ ⊤)
    (hnc : NonConstOnSupport T x) :
    ∃ γ : ℝ, 0 ≤ γ ∧ L T (fun _ => γ) = L T x ∧
      I T (fun _ => γ) < I T x ∧
      ∀ γ' : ℝ, 0 ≤ γ' → L T (fun _ => γ') = L T x → γ' = γ := by sorry

end EvolvHier.SocialOpt
