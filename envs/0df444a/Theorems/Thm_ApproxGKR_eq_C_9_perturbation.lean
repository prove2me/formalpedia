-- Prove2me | Theorems.Thm_ApproxGKR_eq_C_9_perturbation
-- name    : ApproxGKR.eq_C_9_perturbation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:22.348524+00:00
-- url     : https://prove2.me/theorems/cd60acb7-afcc-49da-8058-324f525f9e9b
-- title:
--   (C.9) — the perturbation bound of the gate check
-- statement:
--   1. For complex numbers with $|w^+|,|w^\times|\le W$, $|a|\le U$ and $|\widetilde V(v)|\le R$, writing $e_a=a-\widetilde V(u)$, $e_b=b-\widetilde V(v)$,
--   $$\big|w^+(e_a+e_b)+w^\times(ab-\widetilde V(u)\widetilde V(v))\big|\le W(2+U+R)\max\{|e_a|,|e_b|\}.$$
--   2. In the protocol, for admissible extensions and gate values bounded by $B_V$, every layer $i<L$ and every coins, the hypotheses of item 1 hold with the constants of (C.7): $|w^+_i|,|w^\times_i|\le W=2B_W$ and $|\widetilde V_{i+1}(u_i)|,|\widetilde V_{i+1}(v_i)|\le R=h^mB_V$.
--
--   With $K=W(2+U+R)$ this is $|\dots|\le Ke$: $K$ controls how errors in the claimed evaluations change the gate expression.
--
--   Differences from the source:
--   - generalization: the protocol's w⁺_i, w×_i, a_i, Ṽ_{i+1}(v_i) → any complex numbers with the stated bounds (item 1); reason: item 2 shows the protocol's values satisfy the bounds
--   - encoding: K → W(2 + U + R) written out in item 1; reason: the definition of K in (C.7)
-- source:
--   Das, Gupta, Mondal, More, Delegating Computation with Approximate Arithmetic: Interactive Proofs for Wizards (manuscript, sha256 78b2a36b…), §C.2, eq. (C.9), p.36; eq. (C.7), p.32

import Mathlib
import Definitions.Def_ApproxGKR_AbsAccepts

namespace ApproxGKR

/-- **Equation (C.9): the perturbation bound of the gate check** (p.36).

Das, Gupta, Mondal, More, *Delegating Computation with Approximate Arithmetic* (manuscript,
sha256 78b2a36b…), §C.2, eq. (C.9), p.36: "let `ea = ai − Ṽi+1(ui)` and `eb = bi − Ṽi+1(vi)` be
the errors in the received values, and `e = max{|ea|, |eb|}`. The bounds in Equation (C.7) give
`|w+i(ea + eb) + w×i(aibi − Ṽi+1(ui)Ṽi+1(vi))| ≤ Ke`." "Indeed,
`aibi − Ṽi+1(ui)Ṽi+1(vi) = aieb + Ṽi+1(vi)ea`, with `|ai| ≤ U` and `|Ṽi+1(vi)| ≤ R`."

1. For complex numbers with `|w⁺|, |w×| ≤ W`, `|a| ≤ U`, `|Ṽ(v)| ≤ R`:
   `|w⁺(e_a + e_b) + w×(ab − Ṽ(u)Ṽ(v))| ≤ W(2 + U + R)·max{|e_a|, |e_b|}`.
2. In the protocol (any coins, any layer `i < L`), the bounds of (C.7) hold: `|w⁺ᵢ|, |w×ᵢ| ≤ W`
   and `|Ṽᵢ₊₁(uᵢ)|, |Ṽᵢ₊₁(vᵢ)| ≤ R`, for admissible extensions and gate values bounded by `B_V`.

**Formalization Note** In item 1 `K = W(2 + U + R)` is written out; with the constants of (C.7)
it is `constK`. Only `|a| ≤ U` and `|Ṽ(v)| ≤ R` are assumed, as on the page. -/
theorem eq_C_9_perturbation :
    (∀ (W U R : ℝ) (wp wt a b Vu Vv : ℂ), ‖wp‖ ≤ W → ‖wt‖ ≤ W → ‖a‖ ≤ U → ‖Vv‖ ≤ R →
      ‖wp * ((a - Vu) + (b - Vv)) + wt * (a * b - Vu * Vv)‖ ≤
        W * (2 + U + R) * max ‖a - Vu‖ ‖b - Vv‖) ∧
    (∀ (C : LayeredCircuit) (δ BV BW : ℕ) (ext : ExtFamily C) (x : InputList) (N : ℕ)
      (c : Coins C N) (i : ℕ),
      (∀ i' < C.L, ∀ ty, IsAdmissibleExt C δ BW i' ty (ext i' ty)) → GateBound C x BV →
      i < C.L →
      ‖wplus ext c i‖ ≤ constW BW ∧ ‖wtimes ext c i‖ ≤ constW BW ∧
      ‖MvPolynomial.eval (uPt c i) (Vt C x (i + 1))‖ ≤ constR C.h C.mMax BV ∧
      ‖MvPolynomial.eval (vPt c i) (Vt C x (i + 1))‖ ≤ constR C.h C.mMax BV) := by sorry

end ApproxGKR
