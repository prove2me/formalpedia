-- Prove2me | Theorems.Thm_ByzSigT_Supplement_theorem_5_2
-- name    : ByzSigT.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:50:21.241552+00:00
-- url     : https://prove2.me/theorems/33bccc1e-2880-40ce-8785-b4cb5915e5fd
-- title:
--   Theorem 5.2 — $k$-token lower bound: no $f$-secure BA with a PKI and a $k$-SigT setup for $\frac{2(4^k-1)}{4^{k+1}-1}n \le f < n$, $k \ge 2$
-- statement:
--   Let $k \ge 2$ be an integer, let $n, f$ be positive integers with
--   $$\frac{2(4^k-1)}{4^{k+1}-1}\,n \le f < n,$$
--   and let $\Delta > 0$ be the delay bound of partial synchrony. Then there is no deterministic protocol for Byzantine agreement among $n$ parties, with a PKI and a $k$-SigT setup ($k$ signature tokens per party), that is $f$-secure: for every such well-formed protocol $P$ there are a corrupt set $F$ with $|F| \le f$, inputs, a stabilization time $\mathrm{GST} \ge 0$ and an execution of $P$ in which agreement, termination or validity fails.
--
--   Together with the mission's goal (Theorem 4.1, an $f$-secure protocol for $f < \frac{2^{k+1}-1}{2^{k+2}-1}n$), this shows that the gap between the optimal resilience with $k$ tokens and $n/2$ is $2^{-\Theta(k)}$; in particular $\Theta(\log n)$ tokens per party are necessary and sufficient to tolerate $f < n/2$. The case $k = 1$ is excluded because there the bound would be $2n/5 < 3n/7$, below the threshold of Theorem 5.1.
--
--   **Formalization Note** The statement is $\neg\,\exists P : \mathtt{Protocol}\ n\ k,\ P.\mathtt{WellFormed} \wedge \mathtt{Secure}\ P\ f\ \Delta$, the negation of exactly the conjunction the goal asserts, in the mission's published model. The protocol may depend on $n$, $f$, $k$ and $\Delta$. In $\mathbb N$, $4^k - 1$ never truncates since $4^k \ge 1$.
--
--   Differences from the source:
--   - reading: deterministic protocol in the partially synchronous model with a PKI and a k-SigT setup (§2) → the mission's published model: well-formed symbolic protocols (ideal signatures and tokens, no forgery, timers of length at least some d₀ > 0) and executions in which the adversary sees all honest traffic, may duplicate deliveries and orders simultaneous events; reason: the paper states Theorems 4.1, 5.1 and 5.2 in one model of §2, and the tightness comparison with Theorem 4.1 only holds if the lower bound is stated in the same model as the published goal; §2's prose fixes no finer reading, and these choices leave the impossibility no stronger than the paper's
--   - encoding: 2(4^k−1)/(4^{k+1}−1) n ≤ f → 2·(4^k − 1)·n ≤ (4^{k+1} − 1)·f in ℕ; reason: cross-multiplication by 4^{k+1} − 1 > 0, and 4^k − 1 does not truncate; same instances
--   - encoding: the delay bound Δ, known to the protocol → a universally quantified Δ > 0 before the protocol; reason: the protocol is chosen after Δ, as in the goal; same instances
--   - encoding: values {0, 1} → Bool with 0 = false; reason: Lean convention, same instances
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58aafc3ec9e55ea644823c5ad9a44b6948813ba96a1ea5fce0da8f1540f), Theorem 5.2, p.26 (PDF p.27); informal version Theorem 1.3, p.3 (PDF p.4); model §2, pp.4–6 (PDF 5–7)

import Mathlib
import Definitions.Def_ByzSigT_Secure

namespace ByzSigT.Supplement

open ByzSigT

/-- **Theorem 5.2** (k-token lower bound; p.26, PDF p.27; also Theorem 1.3, p.3). Efron, Kelkar,
Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027 submission (manuscript
sha256 f020c58a…):

> Let k ≥ 2 be an integer and let n, f be positive integers such that
> 2(4^k−1)/(4^{k+1}−1) n ≤ f < n. There is no deterministic f-secure protocol for BA in the
> partially synchronous model with a PKI and a k-SigT setup.

For every `k ≥ 2`, all positive `n, f` with `2(4^k − 1)·n ≤ (4^{k+1} − 1)·f` and `f < n`, and every
delay bound `Δ > 0`, no well-formed deterministic protocol for `n` parties with a `k`-SigT setup
(`Protocol n k`) is `f`-secure.

**Formalization Note.** The model is the published one of the mission (`ByzSigT.Protocol`,
`Protocol.WellFormed`, `ByzSigT.IsExecution`, `ByzSigT.Secure`), the same in which the goal
`ByzSigT.theorem_4_1` asserts `∃ P : Protocol n k, P.WellFormed ∧ Secure P f Δ`; this theorem
negates exactly that conjunction. The protocol may depend on `n, f, k, Δ`. The fraction is
cross-multiplied in `ℕ` (`4^{k+1} − 1 > 0`; `4^k − 1` never truncates since `4^k ≥ 1`). The full
range `f < n` is covered, including `f ≥ n/2`. -/
theorem theorem_5_2 (k : ℕ) (hk : 2 ≤ k) (n f : ℕ) (hn : 0 < n) (hf : 0 < f)
    (hlow : 2 * (4 ^ k - 1) * n ≤ (4 ^ (k + 1) - 1) * f) (hfn : f < n)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    ¬ ∃ P : Protocol n k, P.WellFormed ∧ Secure P f Δ := by sorry

end ByzSigT.Supplement
