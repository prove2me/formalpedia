-- Prove2me | Theorems.Thm_EvolvHier_SocialOpt_step_3
-- name    : EvolvHier.SocialOpt.step_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:22:29.536979+00:00
-- url     : https://prove2.me/theorems/decd8cf8-10e4-4af3-b0bf-7e916839d385
-- title:
--   Step 3 — a nonconstant equilibrium is socially dominated
-- statement:
--   Let $x$ be an equilibrium of a valid scheme. If its expected length is finite and it varies among agents reached with positive probability, then a unique constant profile $y=(\gamma,\gamma,\ldots)$ of that expected length is an equilibrium of a valid scheme and has strictly greater social value:
--
--   $$L(y)=L(x),\qquad V(x)<V(y).$$
--
--   This reduces the search for a socially optimal supporting equilibrium to constant profiles.
--
--   **Formalization Note** The supporting scheme for $y$ may differ from the scheme supporting $x$. Nonconstancy and finiteness use the disclosed reading of Step 2.
-- source:
--   Hougaard, Moreno-Ternero & Østerdal, Optimal Management of Evolving Hierarchies, UPO WP ECON 21.15 (Aug. 3, 2021; Manag. Sci. doi:10.1287/mnsc.2021.4185), proof of Theorem 2, Step 3, pp. 25–26

import Mathlib
import Definitions.Def_EvolvHier_SocialOpt_Setting

namespace EvolvHier.SocialOpt

/-- Proof of Theorem 2, Step 3, with nonconstancy measured on realized agents. -/
theorem step_3 (T : Technology) (t : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (ht : IsScheme t) (hx : IsEquilibrium T t x)
    (hL : L T x ≠ ⊤) (hnc : NonConstOnSupport T x) :
    ∃ γ : ℝ, 0 ≤ γ ∧
      (∃ t', IsScheme t' ∧ IsEquilibrium T t' (fun _ => γ)) ∧
      L T (fun _ => γ) = L T x ∧ V T x < V T (fun _ => γ) ∧
      ∀ γ' : ℝ, 0 ≤ γ' → L T (fun _ => γ') = L T x → γ' = γ := by sorry

end EvolvHier.SocialOpt
