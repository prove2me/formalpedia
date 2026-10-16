-- Prove2me | Theorems.Thm_AgriSubsidy_Combined_prop2_proof_convex
-- name    : AgriSubsidy.Combined.prop2_proof_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T06:17:43.125048+00:00
-- url     : https://prove2.me/theorems/c854f8ff-5070-4858-b1a5-c434c03f2aa1
-- title:
--   Proof of Proposition 2, Online Appendix p. 1 — increasing convex maps preserve weak sub-majorization
-- statement:
--   Let $I$ be a convex subset of the real line, and let $\varphi$ be increasing and convex on $I$. If finite vectors $u,v$ have every coordinate in $I$ and $u\ge_{wm}v$, then
--
--   $$\bigl(\varphi(u_j)\bigr)_j\ge_{wm}\bigl(\varphi(v_j)\bigr)_j.$$
--
--   This is the order property cited in the paper's proof of Proposition 2. In the market application, the positive outputs lie in $[0,\infty)$ and $\varphi(x)=\beta x^2$.
-- source:
--   Fan, Feng, Li, Shanthikumar, Wu, Output-Oriented Agricultural Subsidy Design, SSRN 4378693 (version of 2023-03-18), Online Appendix p. 1, Proof of Proposition 2; cites Marshall et al. (1979), Theorem A.2(i)

import Mathlib
import Definitions.Def_AgriSubsidy_Combined_Setting
import Definitions.Def_AgriSubsidy_Combined_Majorization

namespace AgriSubsidy.Combined

theorem prop2_proof_convex {N : ℕ} (I : Set ℝ) (φ : ℝ → ℝ)
    (hmono : MonotoneOn φ I) (hconv : ConvexOn ℝ I φ)
    (u v : Fin N → ℝ) (hu : ∀ j, u j ∈ I) (hv : ∀ j, v j ∈ I)
    (h : WeakSubMaj u v) :
    WeakSubMaj (fun j => φ (u j)) (fun j => φ (v j)) := by sorry

end AgriSubsidy.Combined
