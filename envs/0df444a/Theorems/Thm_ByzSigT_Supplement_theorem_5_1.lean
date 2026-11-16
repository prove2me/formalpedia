-- Prove2me | Theorems.Thm_ByzSigT_Supplement_theorem_5_1
-- name    : ByzSigT.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:49:51.450302+00:00
-- url     : https://prove2.me/theorems/1dfbc852-82bd-474c-a1e9-07c16bcf8bcc
-- title:
--   Theorem 5.1 — one-token lower bound: no $f$-secure BA with a PKI and a 1-SigT setup for $3n/7 \le f < n$
-- statement:
--   Let $n, f$ be positive integers with
--   $$\frac{3n}{7} \le f < n,$$
--   and let $\Delta > 0$ be the delay bound of partial synchrony. Then there is no deterministic protocol for Byzantine agreement among $n$ parties, with a PKI and a $1$-SigT setup (one signature token per party), that is $f$-secure: for every such well-formed protocol $P$ there are a corrupt set $F$ with $|F| \le f$, inputs, a stabilization time $\mathrm{GST} \ge 0$ and an execution of $P$ in which agreement, termination or validity fails.
--
--   Together with the mission's goal (Theorem 4.1 at $k = 1$, which gives an $f$-secure protocol for $f < 3n/7$), this shows that $3n/7$ is the exact resilience threshold of Byzantine agreement in partial synchrony with one signature token per party.
--
--   **Formalization Note** The statement is $\neg\,\exists P : \mathtt{Protocol}\ n\ 1,\ P.\mathtt{WellFormed} \wedge \mathtt{Secure}\ P\ f\ \Delta$, the negation of exactly the conjunction the goal asserts, in the mission's published model. The protocol may depend on $n$, $f$ and $\Delta$.
--
--   Differences from the source:
--   - reading: deterministic protocol in the partially synchronous model with a PKI and a 1-SigT setup (§2) → the mission's published model: well-formed symbolic protocols (ideal signatures and tokens, no forgery, timers of length at least some d₀ > 0) and executions in which the adversary sees all honest traffic, may duplicate deliveries and orders simultaneous events; reason: the paper states Theorems 4.1, 5.1 and 5.2 in one model of §2, and the tightness at 3n/7 only holds if the lower bound is stated in the same model as the published goal; §2's prose fixes no finer reading, and these choices leave the impossibility no stronger than the paper's
--   - encoding: 3n/7 ≤ f → 3·n ≤ 7·f in ℕ; reason: cross-multiplication by 7 > 0, same instances
--   - encoding: the delay bound Δ, known to the protocol → a universally quantified Δ > 0 before the protocol; reason: the protocol is chosen after Δ, as in the goal; same instances
--   - encoding: values {0, 1} → Bool with 0 = false; reason: Lean convention, same instances
-- source:
--   Efron, Kelkar, Mutreja, Roughgarden, Byzantine Agreement with Signature Tokens, STOC 2027 submission (manuscript sha256 f020c58aafc3ec9e55ea644823c5ad9a44b6948813ba96a1ea5fce0da8f1540f), Theorem 5.1, p.26 (PDF p.27); informal version Theorem 1.2, p.3 (PDF p.4); model §2, pp.4–6 (PDF 5–7)

import Mathlib
import Definitions.Def_ByzSigT_Secure

namespace ByzSigT.Supplement

open ByzSigT

/-- **Theorem 5.1** (one-token lower bound; p.26, PDF p.27; also Theorem 1.2, p.3). Efron, Kelkar,
Mutreja, Roughgarden, *Byzantine Agreement with Signature Tokens*, STOC 2027 submission (manuscript
sha256 f020c58a…):

> Let n, f be positive integers such that 3n/7 ≤ f < n. There is no deterministic f-secure protocol
> for BA in the partially synchronous model with a PKI and a 1-SigT setup.

For all positive `n, f` with `3n ≤ 7f` and `f < n`, and every delay bound `Δ > 0`, no well-formed
deterministic protocol for `n` parties with a 1-SigT setup (`Protocol n 1`) is `f`-secure.

**Formalization Note.** The model is the published one of the mission (`ByzSigT.Protocol`,
`Protocol.WellFormed`, `ByzSigT.IsExecution`, `ByzSigT.Secure`), the same in which the goal
`ByzSigT.theorem_4_1` asserts `∃ P : Protocol n k, P.WellFormed ∧ Secure P f Δ`; this theorem
negates exactly that conjunction for `k = 1`. The protocol may depend on `n, f, Δ`. The fraction
`3n/7 ≤ f` is cross-multiplied in `ℕ`. The full range `f < n` is covered, including `f ≥ n/2`
(which the paper dismisses as folklore, p.29). -/
theorem theorem_5_1 (n f : ℕ) (hn : 0 < n) (hf : 0 < f) (hlow : 3 * n ≤ 7 * f) (hfn : f < n)
    (Δ : ℝ) (hΔ : 0 < Δ) :
    ¬ ∃ P : Protocol n 1, P.WellFormed ∧ Secure P f Δ := by sorry

end ByzSigT.Supplement
