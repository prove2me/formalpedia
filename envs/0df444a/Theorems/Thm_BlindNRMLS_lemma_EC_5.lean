-- Prove2me | Theorems.Thm_BlindNRMLS_lemma_EC_5
-- name    : BlindNRMLS.lemma_EC_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:22.267805+00:00
-- url     : https://prove2.me/theorems/d5fa40ff-0ea2-4d09-885b-9330b4bffa7a
-- title:
--   Lemma EC.5 — after the last cover time at most $K+d-1$ switches remain
-- statement:
--   Let $\phi\in\Phi[s]$ with $\nu=\nu(s,d)\ne0$. Under any demand distributions, almost surely, on the event $E_{\nu+1}=\{\tau_\nu\le t_\nu\}$ the number of switches in $[\tau_\nu:T]$ is at most $K+d-1$.
--
--   The cover times $\tau_1\le\dots\le\tau_\nu$ each consume $K-1$ switches, so what is left after them is too little for a policy that still has to explore.
--
--   Differences from the source:
--   - generalization: for any instance I_µ → for any problem and any Q; reason: the argument only counts switches; I_µ are instances
--   - encoding: τ_ν ≤ t_ν with 1-based times, and E_{ν+1} defined only when ν ≠ 0 → coverTime ν + 1 ≤ t_ν with 0-based rounds, and the hypothesis ν ≠ 0; reason: index shift; same event
--   - generalization: a policy chooses z_t in [K] and the algorithm may stop → actions are Option (Fin K), with none an absorbing stop; reason: Algorithm 2 and Lemma EC.7 stop; a policy never using none is a policy of the page
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, Lemma EC.5, p.ec51; definitions, pp.ec49–50

import Mathlib
import Definitions.Def_BlindNRMLS_hardProblem
import Definitions.Def_BlindNRMLS_nu

open MeasureTheory
open scoped ENNReal

namespace BlindNRMLS

/-- Lemma EC.5: for `ϕ ∈ Φ[s]` with `ν(s,d) ≠ 0`, almost surely, the event
`E_{ν+1} = {τ_ν ≤ t_ν}` implies that at most `K + d - 1` switches occur in `[τ_ν : T]`.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5, Lemma EC.5, p.ec51, with the definitions of p.ec49–50.

**Formalization Note.** The page's `E_{ν+1}` is defined only for `ν ≠ 0`. Cover times are `0`-based, so
the page's `τ_ν ≤ t_ν` is `coverTime … ν + 1 ≤ t_ν`. Actions and switches are the frozen ones. The
statement is for any problem and any `Q`, of which the page's `I_µ` are instances. -/
theorem lemma_EC_5 {d n K : ℕ} (P : Problem d n K) (Q : DemandLaw n K) (s : ℕ) (φ : Policy n K)
    (hφ : φ ∈ LearningClass P s) (hν : nu s d K ≠ 0) :
    ∀ᵐ h ∂(historyLaw Q φ P.T),
      coverTime P h (nu s d K) + 1 ≤ (tSched P.T K (nu s d K) (nu s d K) : ℕ∞) →
        switchesFrom P h (coverTime P h (nu s d K)).toNat ≤ K + d - 1 := by sorry

end BlindNRMLS
