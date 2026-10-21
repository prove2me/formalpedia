-- Prove2me | Theorems.Thm_FlexApproval_Statics_concavity_pieces
-- name    : FlexApproval.Statics.concavity_pieces
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:39.47186+00:00
-- url     : https://prove2.me/theorems/7acf6ac1-3c2f-47b0-a7c1-aadfe16ecf52
-- title:
--   Proof of Theorem 1, p. 33 — ψ_E(α) is concave increasing in α, E[N_E] is concave increasing in ψ_E, so E[N_E(α)] is concave
-- statement:
--   Under the standing assumptions of the drug-approval model, the normalized approval rate of effective drugs
--   $$\psi_E(\alpha)=\frac{\tilde\lambda\,p\,\big[1-\Phi(\Phi^{-1}(1-\alpha)-\delta\sqrt{I_n})\big]}{K\mu_E}$$
--   is concave and nondecreasing on $[0,1]$; the map $\psi\mapsto K\psi/(1+\psi)$ is concave and nondecreasing on $[0,\infty)$; and consequently the expected number of effective drugs on the market, $\mathbb E[N_E(\alpha)]=K\psi_E(\alpha)/(1+\psi_E(\alpha))$, is concave on $[0,1]$.
--
--   These are the facts the paper's proof of Theorem 1 cites ("direct computation shows"), and the monotonicity of $\psi_E$ is used again in (A.18).
--
--   **Formalization Note** The power curve takes its limit values $0$ and $1$ at $\alpha=0$ and $\alpha=1$ (see the model definition). "Increasing" is stated as weak monotonicity.
-- source:
--   Bravo, Corcoran & Long, Flexible Drug Approval Policies, SSRN working paper 3027263 (version of 17 Jul 2019), p. 33, proof of Theorem 1

import Mathlib
import Definitions.Def_FlexApproval_Statics_Model

namespace FlexApproval.Statics

open Cohen2019.Robust

/-- Proof of Theorem 1, p. 33: `ψ_E(α)` is concave (and increasing) in `α` on `[0, 1]`;
`ψ ↦ Kψ/(1 + ψ)` is concave and increasing on `[0, ∞)`; hence `E[N_E(α)]` is concave on `[0, 1]`. -/
theorem concavity_pieces (P : Params) (hP : P.Standing) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (psiE P) ∧ MonotoneOn (psiE P) (Set.Icc (0 : ℝ) 1) ∧
    ConcaveOn ℝ (Set.Ici (0 : ℝ)) (fun ψ : ℝ => (P.K : ℝ) * ψ / (1 + ψ)) ∧
    MonotoneOn (fun ψ : ℝ => (P.K : ℝ) * ψ / (1 + ψ)) (Set.Ici (0 : ℝ)) ∧
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (ENE P) := by sorry

end FlexApproval.Statics
