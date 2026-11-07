-- Prove2me | Theorems.Thm_CompPermOracle_corollary_4_3
-- name    : CompPermOracle.corollary_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:08.247124+00:00
-- url     : https://prove2.me/theorems/8a2b6014-203b-4e8f-9aba-7179f6105648
-- title:
--   Corollary 4.3 — $q$ queries distinguish $\mathrm{cpO}$ from a random permutation with advantage at most $120q/\sqrt{N-q+1}+q(q+1)/(N-2q+1)$
-- statement:
--   Let $A$ be an arbitrary quantum algorithm making $q$ forward and/or inverse queries, where $3q-1\le N$, and outputting a decision bit. The distinguishing advantage between the compressed permutation oracle and an ideal permutation is bounded by
--   $$
--   \Big|\Pr_{\varphi\sim S_N}\big[1\leftarrow A^{\tilde O_\varphi,\tilde O_{\varphi^{-1}}}\big]-\Pr\big[1\leftarrow A^{\mathrm{cpO}}\big]\Big|\le\frac{120q}{\sqrt{N-q+1}}+\frac{q(q+1)}{N-2q+1}.
--   $$
--   In particular, constant distinguishing advantage requires $q=\Omega(\sqrt N)$: for every $\varepsilon>0$ there is $c>0$ such that for all $N$, $q$ and all algorithms, advantage at least $\varepsilon$ implies $q\ge c\sqrt N$.
--
--   So the compressed permutation oracle is sound up to the square-root query scale, with explicit constants for concrete security.
--
--   Differences from the source:
--   - reading: $\mathcal O_\varphi,\mathcal O_{\varphi^{-1}}$ in (13); (1) on p.6 uses this letter for the additive oracle → the swap oracles $\tilde O_\varphi,\tilde O_{\varphi^{-1}}$ of Definition 3.1; reason: the same algorithm must run against cpO, which acts on $\mathcal A$ by swaps; "We will work exclusively with swap oracles" (p.6); the proof compares against $P$ of Remark 3.3
--   - reading: constant distinguishing advantage requires $q=\Omega(\sqrt N)$ → for all $\varepsilon>0$ there is $c>0$, chosen before $N,q,W,A$, such that advantage $\ge\varepsilon$ implies $c\sqrt N\le q$; no hypothesis on $q$; reason: the standard meaning of the $\Omega$; for $3q-1>N$ the conclusion follows from $q\ge(N+1)/3$, and the corollary excludes no algorithm here
--   - generalization: q forward and/or inverse queries → each oracle step coherently controlled on a direction bit, with an arbitrary unit initial state and an arbitrary finite workspace; reason: a fixed schedule is the case where the algorithm sets the bit classically; Lemma 5.2 of the source uses coherent choices of direction
--   - encoding: arbitrary quantum algorithm outputting a decision bit → unit initial state, unitaries on the accessible registers, a set of accepting basis states; mid-circuit measurements deferred; reason: the standard unitary query model; any decision measurement is a basis measurement after a unitary, as $W$ is arbitrary
--   - encoding: $3q-1\le N$ → `3 * q ≤ N + 1`; reason: no truncated subtraction
--   - encoding: $[N]=\{1,\dots,N\}$, blank symbol $\bot$ → `Fin N` (0-based), $\bot$ = `none`; reason: a relabelling; no index appears in the bound
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), Corollary 4.3, p.12

import Mathlib
import Definitions.Def_CompPermOracle_Alg

namespace CompPermOracle

/-- Corollary 4.3 (Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), p.12): the
distinguishing advantage bound (13), and "In particular, constant distinguishing advantage requires
`q = Ω(√N)`".

**Formalization Note.** The oracle `𝒪` in (13) is the swap oracle `Õ` of Definition 3.1. An algorithm
(`Alg`) has an arbitrary finite workspace `W`, an arbitrary unit initial state on the accessible
registers, arbitrary unitaries on them, and direction-controlled oracle steps. `3q − 1 ≤ N` is
`3q ≤ N + 1`. In the second clause, `c` depends on `ε` only, it is chosen before `N`, `q`, `W` and the
algorithm, and no hypothesis on `q` is added. -/
theorem corollary_4_3 :
    (∀ (N q : ℕ) (W : Type) [Fintype W] [DecidableEq W] (A : Alg N W), 3 * q ≤ N + 1 →
      |idealAccept A q - compressedAccept A q| ≤
        120 * (q : ℝ) / Real.sqrt ((N : ℝ) - q + 1) +
          (q : ℝ) * ((q : ℝ) + 1) / ((N : ℝ) - 2 * q + 1)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
      ∀ (N q : ℕ) (W : Type) [Fintype W] [DecidableEq W] (A : Alg N W),
        ε ≤ |idealAccept A q - compressedAccept A q| → c * Real.sqrt (N : ℝ) ≤ q) := by sorry

end CompPermOracle
