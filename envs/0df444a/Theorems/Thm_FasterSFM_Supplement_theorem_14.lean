-- Prove2me | Theorems.Thm_FasterSFM_Supplement_theorem_14
-- name    : FasterSFM.Supplement.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:53:32.124633+00:00
-- url     : https://prove2.me/theorems/9cccd311-d1b5-41b4-ac25-a98b74729b40
-- title:
--   Theorem 14 — the cutting plane method makes at most $Q_n=k_n+n=O(n\log(n+2))$ separation-oracle calls
-- statement:
--   Let $n\ge1$, let $U=\{0,\dots,n-1\}$ and let $h:2^U\to\mathbb R$ be submodular. Consider the exact cutting plane method of §8 (separation oracle of §4.2, wide steps and thin events of §5.4, certificates of Lemmas 15–16, arc extraction of Lemmas 6–7, recentering of §7), run on $h$. Then at every point of every run, the number $q$ of separation-oracle calls made so far, counted over all contractions and including graph-only calls and the terminal call, satisfies
--
--   $$
--   q\;\le\;Q_n=k_n+n,\qquad k_n=\frac{8n}{\gamma}\log\frac{1+2/\gamma}{\delta^2},\quad \delta=(K(n+1))^{-20},
--   $$
--
--   with $\gamma=2^{-28}$ and $K=2^{100}$. Moreover $Q_n=O(n\log(n+2))$: there is a constant $C>0$ with $Q_n\le C\,n\log(n+2)$ for every $n\ge1$.
--
--   This is the bound that turns the cutting plane method into an $O(n^2\log n)$ value-oracle algorithm: each oracle call costs at most $n-1$ evaluations, and the query part of Theorem 1 follows from it.
--
--   **Formalization Note** The run of the algorithm is the transition relation `FasterSFM.Supplement.Step`, and "every point of every run" is every state reachable from an initial state. Where the paper leaves a choice, the relation allows every choice with the property the paper's construction guarantees, so the bound is asserted for all of these runs. $Q_n$ is the published `FasterSFM.Qn`.
--
--   Differences from the source:
--   - generalization: the paper's algorithm with its own choices → every run of `Step`, where the violated arc, the tie order, the number of Newton steps, the coefficients of Lemma 15, the target, the arc head, the query sets of Lemma 7's search, $\Gamma$ and the block numbering range over all choices with the properties the paper's constructions guarantee; reason: the paper's run is one of these runs, so the statement specializes to the source; the counting argument (Lemmas 11, 13 and the step-5 loop of Lemma 8) uses only these properties.
--   - generalization: in step 5 the algorithm may halt when the queries of the arc search reach $\Delta\ge\beta$ ("can terminate", p.15) → both halting and adding the arc are allowed; reason: more runs; the paper's run is among them.
--   - generalization: the zero test after a contraction applies to "every compressed stored vector" → to the stored greedy vectors of the inserted rows; reason: fewer halting transitions only add runs; a halted paper run is a prefix of a run of `Step`.
--   - encoding: "over all contractions", every finite execution prefix (p.26) → every reachable state, with a call counter that is never reset; reason: same claim.
--   - encoding: $O(n\log(n+2))$ → $\exists C>0\ \forall n\ge1,\ Q_n\le C n\log(n+2)$; reason: the asymptotic statement with an explicit constant.
--   - encoding: ground set of size $n$, $h$ submodular → `Fin n` with $n\ge1$, $h$ real valued and submodular in the sense of the published `NonmonotoneSubmod.Shared.Submodular`; reason: a relabelling; the paper's setting.
--   - encoding: the state holds the witness set $X_{\mathrm{out}}$ and value caches → neither is stored; reason: no step branches on them (only on $m$), and value-oracle calls are not counted here.
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, Theorem 14, §5.6, p.25 (proof p.26)

import Mathlib
import Definitions.Def_FasterSFM_Params
import Definitions.Def_FasterSFM_Supplement_Run
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace FasterSFM.Supplement

open FasterSFM

/-- **Theorem 14** (Bound on oracle calls), p.25.

Ene & Nguyen, arXiv:2610.25403v1, Theorem 14, §5.6, p.25 (proof p.26: "The same argument bounds
every finite execution prefix. The count includes graph-only calls").

"The cutting plane method makes at most Q_n = k_n + n = O(n log(n + 2)) separation oracle calls
over all contractions."

For every `n ≥ 1`, every submodular `h : 2^{Fin n} → ℝ` and every state `s` reachable by the
algorithm of §8 (the run relation `Reachable h`), the number of separation-oracle calls made so far
(graph-only calls and the terminal call included, never reset at a contraction) is at most
`Q_n = k_n + n` with the paper's constants (`FasterSFM.Qn`); and `Q_n = O(n log(n + 2))`.

**Formalization Note.**
* The ground set is `Fin n`, `h` is real valued and submodular in the sense of the published
  `NonmonotoneSubmod.Shared.Submodular` (no normalization, no integrality).
* `O(n log(n + 2))` is: there is `C > 0` with `Q_n ≤ C n log(n + 2)` for every `n ≥ 1`.
* Where the paper leaves a choice, `Step` allows every choice with the property the paper's
  construction guarantees (see `FasterSFM.Supplement.Step`), so the bound is asserted for every such
  run, the paper's own run among them. -/
theorem theorem_14 :
    (∀ (n : ℕ), 1 ≤ n → ∀ h : Finset (Fin n) → ℝ, NonmonotoneSubmod.Shared.Submodular h →
      ∀ s : State n, Reachable h s → (s.calls : ℝ) ≤ Qn n) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → Qn n ≤ C * n * Real.log ((n : ℝ) + 2)) := by sorry

end FasterSFM.Supplement
