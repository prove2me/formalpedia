-- Prove2me | Theorems.Thm_DeterioratingJobs_Makespan_lemma1_interchange
-- name    : DeterioratingJobs.Makespan.lemma1_interchange
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:08:01.950378+00:00
-- url     : https://prove2.me/theorems/5a55b60c-d4ab-4d50-bc63-d1f2b05ec619
-- title:
--   Lemma 1 — the sum (1) is minimized (maximized) by ordering by increasing (decreasing) $\mu_i/[\gamma_i-1]$
-- statement:
--   Let $\mu_1,\dots,\mu_N$ be real numbers and $\gamma_1,\dots,\gamma_N$ real numbers with $\gamma_i>1$ for every $i$. For a permutation $\pi$ of $\{1,\dots,N\}$ write
--
--   $$
--   F(\pi) = \sum_{i=1}^{N} \mu_{\pi(i)} \prod_{r=i+1}^{N} \gamma_{\pi(r)}
--   $$
--
--   for the sum (1). Then:
--
--   1. if $\pi$ lists the jobs by increasing values of $\mu_i/[\gamma_i-1]$, that is, $\mu_{\pi(1)}/[\gamma_{\pi(1)}-1] \le \mu_{\pi(2)}/[\gamma_{\pi(2)}-1] \le \dots \le \mu_{\pi(N)}/[\gamma_{\pi(N)}-1]$, then $F(\pi)\le F(\sigma)$ for every permutation $\sigma$;
--   2. if $\pi$ lists the jobs by decreasing values of $\mu_i/[\gamma_i-1]$, then $F(\sigma)\le F(\pi)$ for every permutation $\sigma$.
--
--   This is the lemma (attributed to Rau 1971) on which all index rules of the paper rest: each deterioration model has an objective of the form (1), and the lemma turns it into an index policy.
--
--   **Formalization Note** The paper says "the permutation ordered by increasing (decreasing) values"; with ties several permutations qualify, so the statement is made for every permutation along which the index is (non-strictly) monotone. The hypothesis $\gamma_i>1$ is not printed in the lemma; the paper applies it only with $\gamma_i=1+\alpha_i$ or $(1+\alpha_i)^2$, and without it the lemma is false (and $\mu_i/[\gamma_i-1]$ divides by zero at $\gamma_i=1$). $\mu$ is unrestricted. Positions are 0-based.
-- source:
--   Browne, Yechiali, Scheduling Deteriorating Jobs on a Single Processor, Oper. Res. 38 (1990), p. 495, Lemma 1

import Mathlib
import Definitions.Def_DeterioratingJobs_Makespan_InterchangeSum

namespace DeterioratingJobs.Makespan

/-- Lemma 1 (Browne–Yechiali 1990, p. 495). For `γ_i > 1`, the sum (1)
`∑_i μ_{π(i)} ∏_{r>i} γ_{π(r)}` is minimized over all permutations by any permutation that lists the
jobs by increasing `μ_i / (γ_i - 1)`, and maximized by any that lists them by decreasing values. -/
theorem lemma1_interchange {N : ℕ} (μ γ : Fin N → ℝ) (hγ : ∀ i, 1 < γ i)
    (π : Equiv.Perm (Fin N)) :
    (Monotone (fun k : Fin N => μ (π k) / (γ (π k) - 1)) →
        ∀ σ : Equiv.Perm (Fin N), lemma1Sum μ γ π ≤ lemma1Sum μ γ σ) ∧
      (Antitone (fun k : Fin N => μ (π k) / (γ (π k) - 1)) →
        ∀ σ : Equiv.Perm (Fin N), lemma1Sum μ γ σ ≤ lemma1Sum μ γ π) := by sorry

end DeterioratingJobs.Makespan
