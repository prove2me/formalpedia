-- Prove2me | Theorems.Thm_ApproxGKR_eq_C_16_soundness
-- name    : ApproxGKR.eq_C_16_soundness
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:42.286842+00:00
-- url     : https://prove2.me/theorems/f12b6591-d4e7-4ea8-8730-17d05ec83b0a
-- title:
--   (C.16) — soundness of approximate GKR against every adaptive prover
-- statement:
--   Let the extensions be admissible, let every gate value have modulus at most $B_V$, let $\Delta_0\ge0$, $0<\alpha,\beta<1$ and $N\ge1$, and let $E_0$ be the threshold of (C.14)–(C.15) with $K$ of (C.7). If
--   $$|y-C(x)|>E_0,$$
--   then for every adaptive prover (unbounded, deterministic, seeing only earlier coins) and every verifier implementation with errors at most $\Delta_0$, the protocol accepts with probability at most
--   $$kD\big(\alpha^{1/D}+N^{-1}\big)+L\big(\beta+N^{-1}\big)\tag{C.16}$$
--   over the uniform coin tuple ($k+L$ independent coins in $\Omega_N$).
--
--   Together with the parameter choice (C.17)–(C.18) this gives the soundness of Theorem C.1.
--
--   Differences from the source:
--   - generalization: N the power of two of (C.17), 0 < ∆₀ ≤ 1 → any N ≥ 1 and any ∆₀ ≥ 0; reason: the argument uses neither
--   - generalization: the paper's verifier → every verifier implementation within ∆₀; reason: the paper's verifier is one of them
--   - encoding: acceptance probability; provers of unbounded power → the number of accepting coin tuples at most |Coins|·(C.16); deterministic adapted provers; reason: a randomized prover is a mixture of deterministic ones
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.3, eqs. (C.14)–(C.16), pp.38–39

import Mathlib
import Definitions.Def_ApproxGKR_AbsAccepts
import Definitions.Def_ApproxGKR_E0

namespace ApproxGKR

open Classical in
/-- **Equation (C.16): soundness of approximate GKR against every adaptive prover**
(pp.38–39).

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §C.3, pp.38–39: "Fix `0 < β < 1`, set `EL = 5∆0`, and define
`t_{i,ki} = (K + 4)∆0 + K(E_{i+1} + ∆0)/β`, (C.14) `t_{i,j−1} = 7∆0 + h(t_{i,j} + ∆0)/α`
(`j = ki, …, 1`), `Ei = t_{i,0}`. (C.15)" "Summing the probabilities that the error first falls at
or below its required threshold while the corresponding check accepts, over all rounds and layers,
bounds acceptance by `kD(α^{1/D} + N^{−1}) + L(β + N^{−1})` (C.16) whenever `|y − C(x)| > E0`. The
argument conditions only on messages already sent and places no restriction on the prover's
computational power or adaptive strategy."

For admissible extensions, gate values bounded by `B_V`, every `∆₀ ≥ 0`, `0 < α, β < 1`, `N ≥ 1`,
every adaptive prover and every verifier implementation with errors at most `∆₀`: if
`|y − C(x)| > E₀` (with `K` of (C.7)), the number of accepting coin tuples is at most
`N^{k+L}·[kD(α^{1/D} + 1/N) + L(β + 1/N)]`.

**Formalization Note** The coin tuple has `k + L` uniform entries in `Fin N`
(`Fintype.card (Coins C N) = N^{k+L}`); probabilities are counts. The prover is deterministic,
sees only earlier coins (`Adapted`), and is otherwise arbitrary. -/
theorem eq_C_16_soundness (C : LayeredCircuit) (δ BV BW : ℕ) (ext : ExtFamily C)
    (x : InputList) (y : ℂ) (N : ℕ) (Δ₀ α β : ℝ) (P : AbsProver C N) (V : AbsVerifier C N)
    (hBV : 1 ≤ BV) (hBW : 1 ≤ BW)
    (hext : ∀ i < C.L, ∀ ty, IsAdmissibleExt C δ BW i ty (ext i ty))
    (hval : GateBound C x BV) (hN : 1 ≤ N) (hΔ₀ : 0 ≤ Δ₀)
    (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hP : P.Adapted) (hV : V.Within P ext x y Δ₀)
    (hy : E0 C (constK C.h C.mMax BV BW) α β Δ₀ < ‖y - output C x‖) :
    ((Finset.univ.filter (fun c : Coins C N => AbsAccepts P V y δ BV BW Δ₀ c)).card : ℝ) ≤
      (Fintype.card (Coins C N) : ℝ) *
        ((C.k : ℝ) * C.Dpar δ * (α ^ ((1 : ℝ) / C.Dpar δ) + 1 / N) + C.L * (β + 1 / N)) := by sorry

end ApproxGKR
