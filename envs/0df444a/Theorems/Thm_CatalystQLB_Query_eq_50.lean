-- Prove2me | Theorems.Thm_CatalystQLB_Query_eq_50
-- name    : CatalystQLB.Query.eq_50
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:21:48.129262+00:00
-- url     : https://prove2.me/theorems/8966b205-9daf-4418-9154-7dd46678ad31
-- title:
--   Eq. (50) — random-function inversion bound $\mathrm{succ}_{\mathrm{inv}}\le(2T+1)^2/2^\lambda$
-- statement:
--   Let $\mathcal I$ be an inverter that receives $z=g(x)$ and makes $T$ queries to $O_g$, for a uniformly random $g:\{0,1\}^\lambda\to\{0,1\}^\lambda$ and a uniform $x\in\{0,1\}^\lambda$. Then
--   $$\mathrm{succ}_{\mathrm{inv}}=\Pr_{g,x}\big[\mathcal I^g(g(x))=x\big]\le\frac{(2T+1)^2}{2^\lambda}.$$
--   The workspace of $\mathcal I$ is arbitrary.
--
--   This is the bound that closes both lower-bound proofs: the inverter built from a circuit makes at most $q_g$ queries to $g$, so its success is at most $(2q_g+1)^2/2^\lambda$.
--
--   Differences from the source:
--   - generalization: the bound applied to the paper's inverter $\mathcal I$ with at most $q_g$ queries → every `Inverter` with $T$ queries, bound $(2T+1)^2/2^\lambda$; reason: the paper invokes the general random-function inversion bound; its inverter is one instance, with $T\le q_g$ and $(2T+1)^2\le(2q_g+1)^2$
--   - reading: the inversion algorithm $\mathcal I$ (receives $z=g(x)$, queries $O_g$, samples its own $i$ and $f$, runs the tests $\{\Pi^\perp,\Pi\}$, measures $Q$, may abort) → `Inverter n W T`: for each $z$ a $T$-query `QAlgorithms.QueryAlg` on $(Q\times R)\times W$ with an arbitrary finite workspace $W$, a final computational-basis measurement and an output map to `Option` strings (`none` = abort); reason: randomness and intermediate measurements are purified into the workspace (deferred measurement), so the class contains the paper's inverter; the inverter never gets $x$ or $O_f$
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Eq. (50), p.47 (PDF 50); Eq. (66), p.52 (PDF 55)

import Mathlib
import Definitions.Def_CatalystQLB_Query_Inverter

namespace CatalystQLB.Query

open QAlgorithms

/-- **Eq. (50)**, the random-function inversion bound (arXiv:2609.40323 (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, version of 2026-11-03), §5.3, Lemma 75's proof, p.47
(PDF 50); restated as Eq. (66), p.52 (PDF 55)): every inverter that receives `z = g(x)` and
makes `T` queries to `O_g` outputs `x` with probability, averaged over a random
`g : {0,1}^n → {0,1}^n` and a uniform `x`, at most `(2T + 1)² / 2^n`.

**Formalization Note** `n` is the paper's `λ`; `T` is the paper's `q_g` (an inverter with at
most `q_g` queries is one with exactly `T ≤ q_g`). The workspace `W` is arbitrary. -/
theorem eq_50 {n : ℕ} {W : Type} [Fintype W] [DecidableEq W] {T : ℕ} (I : Inverter n W T) :
    I.invSuccess ≤ (2 * (T : ℝ) + 1) ^ 2 / 2 ^ n := by sorry

end CatalystQLB.Query
