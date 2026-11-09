-- Prove2me | Theorems.Thm_CEPolytopeHard_eq_14
-- name    : CEPolytopeHard.eq_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:19:30.80081+00:00
-- url     : https://prove2.me/theorems/ab0a90ab-5945-4da9-9313-41fdd1ef46f8
-- title:
--   Copy map and Eq. (14) — $\|\tilde g(z^{(1)},\dots,z^{(q)}) - g(x)\|_2 \le 3q\sqrt{\sum_j\|z^{(j)}-x\|_2^2}$
-- statement:
--   Let $C$ be a well-formed generalized circuit with fan-out two and $d$ nodes, $0 < \tau < 1/4$, $\lambda = \max\{1, 1/(2\tau)\}$, $p \ge (4\lambda/\tau)^2$, $q = 2p + 1$, $f$ the circuit's polynomial map, $b \ge 1$ an integer and $g$ the lift of $f$ with base $b$ and $r$ layers. Then
--
--   1. $\tilde f_i$ takes values in $[0,1]$ for copies in $[0,1]^d$ (even when they disagree), and $\tilde f_i(x, \dots, x) = f_i(x)$;
--   2. $\tilde g$ takes values in $[0,1]^{dr}$ for copies in $[0,1]^{dr}$, and $\tilde g(x, \dots, x) = g(x)$;
--   3. for all copies $z^{(1)}, \dots, z^{(q)}$ and $x$ in $[0,1]^{dr}$ (normalized norms),
--   $$
--   \|\tilde g(z^{(1)}, \dots, z^{(q)}) - g(x)\|_2 \le 3q\sqrt{\sum_{j=1}^q \|z^{(j)} - x\|_2^2}. \tag{14}
--   $$
--
--   This lets the constructed game evaluate $g$ through multilinear utilities, as long as the copies stay close to $x$.
--
--   Differences from the source:
--   - generalization: b as in (12) (an integer b ≥ 2) → any integer b ≥ 1; reason: the claims hold for every b ≥ 1 and specialize to (12)
--   - encoding: copies z^{(1)}, …, z^{(q)} with copy q retained; layers ℓ = 1, …, r → copies indexed 0, …, 2p (Fin.last (2p) is copy q); 0-based layers with weight b^{−(ℓ+1)}; reason: Lean indexing
--   - reading: "for a constant λ ≥ 1" (unnamed, p.20) in p ≥ (4λ/τ)² → λ = lam τ = max{1, 1/(2τ)}; reason: the least constant ≥ 1 that is a Lipschitz constant of every Section 2.5 gate map
--   - reading: the circuit of [71], whose gate maps on p.20 include OR, AND, NOT → any well-formed fan-out-two circuit of the Section 2.5 class (no Boolean gates); reason: Section 2.5 defines no Boolean gate type (see the [71] item); fan-out two is within "each input occurs at most three times in a fixed copy"
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), "Evaluating the map with copies", Eq. (14), p.22

import Mathlib
import Definitions.Def_CEPolytopeHard_GCircuit
import Definitions.Def_CEPolytopeHard_gateMap
import Definitions.Def_CEPolytopeHard_circuitMap
import Definitions.Def_CEPolytopeHard_nnorm
import Definitions.Def_CEPolytopeHard_liftG
import Definitions.Def_CEPolytopeHard_gtilde

set_option autoImplicit false

namespace CEPolytopeHard

/-- **The copy map and Eq. (14)** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, "Evaluating the map with copies", p.22: "This multilinear
polynomial takes values in [0, 1] even when the copies disagree, and equals f_i(x) when all copies
equal x. … This map takes values in [0, 1]^{dr} and equals g(x) when all copies equal x. Since each
output uses at most q inputs and each input occurs at most three times in a fixed copy,
Cauchy-Schwarz yields ∥g̃(z^{(1)}, . . . , z^{(q)}) − g(x)∥₂ ≤ 3q √(∑_{j=1}^q ∥z^{(j)} − x∥₂²). (14)").

Let `C` be a well-formed fan-out-two generalized circuit, `0 < τ < 1/4`, `λ = max{1, 1/(2τ)}`,
`p ≥ (4λ/τ)²`, `q = 2p + 1`, `f` the circuit's polynomial map, `b ≥ 1` and `g` the lift of `f` with
base `b` and `r` layers. Then
1. `f̃_i` takes values in `[0, 1]` for copies in `[0, 1]^d`, and `f̃_i(x, …, x) = f_i(x)` for
   `x ∈ [0, 1]^d`;
2. `g̃` takes values in `[0, 1]^{dr}` for copies in `[0, 1]^{dr}`, and `g̃(x, …, x) = g(x)` for
   `x ∈ [0, 1]^{dr}`;
3. (14) holds for all copies `z^{(1)}, …, z^{(q)}` and `x` in `[0, 1]^{dr}` (normalized norms).

**Formalization Note** The paper takes `b` from (12) (`b ≥ 2`); every integer `b ≥ 1` is allowed
here. Copies are 0-based, the last one (`Fin.last (2p)`) is the paper's copy `q`. -/
theorem eq_14 (C : GCircuit) (hwf : C.WellFormed) (hfo : C.FanOutTwo) (τ : ℝ) (hτ0 : 0 < τ)
    (hτ1 : τ < 1 / 4) (p : ℕ) (hp : (4 * lam τ / τ) ^ 2 ≤ (p : ℝ)) (b : ℕ) (hb : 1 ≤ b) (r : ℕ) :
    (∀ z : Fin (2 * p) → Fin C.d → ℝ, (∀ j, z j ∈ Set.Icc (0 : Fin C.d → ℝ) 1) → ∀ i,
      ftilde τ p C z i ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ x ∈ Set.Icc (0 : Fin C.d → ℝ) 1, ∀ i, ftilde τ p C (fun _ => x) i = circuitMap τ p C x i) ∧
    (∀ z : Fin (2 * p + 1) → Fin r × Fin C.d → ℝ,
      (∀ j, z j ∈ Set.Icc (0 : Fin r × Fin C.d → ℝ) 1) →
        gtilde τ p C b z ∈ Set.Icc (0 : Fin r × Fin C.d → ℝ) 1) ∧
    (∀ x ∈ Set.Icc (0 : Fin r × Fin C.d → ℝ) 1,
      gtilde τ p C b (fun _ => x) = liftG b (circuitMap τ p C) x) ∧
    ∀ (z : Fin (2 * p + 1) → Fin r × Fin C.d → ℝ) (x : Fin r × Fin C.d → ℝ),
      (∀ j, z j ∈ Set.Icc (0 : Fin r × Fin C.d → ℝ) 1) → x ∈ Set.Icc (0 : Fin r × Fin C.d → ℝ) 1 →
        nnorm (gtilde τ p C b z - liftG b (circuitMap τ p C) x) ≤
          3 * ((2 * p + 1 : ℕ) : ℝ) * Real.sqrt (∑ j, nnorm (z j - x) ^ 2) := by sorry

end CEPolytopeHard
