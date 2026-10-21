-- Prove2me | Theorems.Thm_DynFairDiv_Uniform_lemma_1
-- name    : DynFairDiv.Uniform.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:53.653701+00:00
-- url     : https://prove2.me/theorems/d3ec507d-394e-4fa0-bb38-54dc7a64fe2e
-- title:
--   Lemma 1, p. 951 — the allocations of FFA(ψ,σ) are those of FFA(ψ,σ′) scaled by σ/σ′
-- statement:
--   Let $\psi$ be a control vector and $\sigma, \sigma' \in \mathbb{R}$ with $\sigma' \neq 0$. For every number of users $t$, the allocation of the frugally fair algorithm with ratio $\sigma$ is the allocation with ratio $\sigma'$ multiplied entrywise by $\sigma/\sigma'$:
--   $$\mathrm{FFA}(\psi,\sigma)^t \;=\; \frac{\sigma}{\sigma'}\,\mathrm{FFA}(\psi,\sigma')^t .$$
--   In particular $S^t(\psi,\sigma) = \frac{\sigma}{\sigma'} S^t(\psi,\sigma')$, which is how the optimal fairness ratio is read off a single run of FFA with $\sigma = 1$.
--
--   **Formalization Note.** FFA's allocation at time $t$ is the list of its shares in nonincreasing order, and the identity holds as an equality of lists. The hypothesis $\sigma' \neq 0$ is added because the statement divides by $\sigma'$.
-- source:
--   Vardi, Psomas, Friedman, Dynamic Fair Resource Division, Math. Oper. Res. 47(2):945–968 (2022), p. 951, Lemma 1 (proof p. 958, Appendix D)

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

namespace DynFairDiv.Uniform

theorem lemma_1 (ψ : ℕ → ℕ) (σ σ' : ℝ) (hσ' : σ' ≠ 0) (t : ℕ) :
    ffa ψ σ t = (ffa ψ σ' t).map (fun x => x * (σ / σ')) := by sorry

end DynFairDiv.Uniform
