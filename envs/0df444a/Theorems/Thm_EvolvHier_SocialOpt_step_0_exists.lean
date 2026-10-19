-- Prove2me | Theorems.Thm_EvolvHier_SocialOpt_step_0_exists
-- name    : EvolvHier.SocialOpt.step_0_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:21.687922+00:00
-- url     : https://prove2.me/theorems/9792655c-892a-4dbd-9dd9-0065eba52b35
-- title:
--   Step 0 — bounded restriction and attainment of maximum length
-- statement:
--   Fix an expected investment $X\geq0$. Every feasible profile $x$ with $I(x)=X$ can be replaced by a profile $z$ with the same expected investment, each $z_i\leq X$, and $L(z)\geq L(x)$. Consequently, the largest attainable expected length is finite and is attained:
--
--   $$L_{\max}(X)<\infty,\qquad \exists x:\ I(x)=X,\quad L(x)=L_{\max}(X).$$
--
--   This gives an actual maximizing profile for later arguments about the length frontier.
-- source:
--   Hougaard, Moreno-Ternero & Østerdal, Optimal Management of Evolving Hierarchies, UPO WP ECON 21.15 (Aug. 3, 2021; Manag. Sci. doi:10.1287/mnsc.2021.4185), proof of Theorem 2, Step 0, p. 21

import Mathlib
import Definitions.Def_EvolvHier_SocialOpt_Setting

namespace EvolvHier.SocialOpt

/-- Proof of Theorem 2, Step 0: bounded restriction and attainment of the
highest expected length at an exact investment level. -/
theorem step_0_exists (T : Technology) (X : ℝ) (hX : 0 ≤ X) :
    (∀ x, IsProfile x → I T x = ENNReal.ofReal X →
      ∃ z, IsProfile z ∧ (∀ k, z k ≤ X) ∧ I T z = ENNReal.ofReal X ∧
        L T x ≤ L T z) ∧
    Lmax T X ≠ ⊤ ∧
      ∃ x, IsProfile x ∧ I T x = ENNReal.ofReal X ∧ L T x = Lmax T X := by sorry

end EvolvHier.SocialOpt
