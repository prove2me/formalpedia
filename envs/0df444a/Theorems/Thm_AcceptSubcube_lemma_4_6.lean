-- Prove2me | Theorems.Thm_AcceptSubcube_lemma_4_6
-- name    : AcceptSubcube.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:10.472526+00:00
-- url     : https://prove2.me/theorems/d9329d88-3c76-42b9-8618-a1ee9f3d1e65
-- title:
--   Lemma 4.6 — rounding of [ACMM05] for Min-2-CNF Deletion
-- statement:
--   There are an absolute constant $c_A$ and a randomized polynomial-time procedure with the following property. Given a nonnegative integer-weighted unary/binary CNF $\Phi$ on $q$ variables and unit vectors $v_0,\dots,v_q$ satisfying the squared-Euclidean triangle inequalities on $\{\pm v_0,\dots,\pm v_q\}$, at which the objective of (15) has value $W$, it outputs with probability at least $3/4$ an assignment of cost at most
--   $$c_A\sqrt{\log(q+2)}\;W .$$
--
--   The vectors are given by their rational Gram matrix. This is the imported rounding of Agarwal, Charikar, Makarychev and Makarychev (STOC 2005), used in cubic repair.
--
--   Differences from the source:
--   - reading: given … unit vectors v₀, …, v_q → given their rational Gram matrix, positive semidefinite with unit diagonal and all signed triangle inequalities; W is (15) through the Gram entries; reason: vectors cannot be machine input; the only use (§4.8, p.21) passes a principal submatrix of the rational moment matrix
--   - reading: a randomized polynomial-time procedure … with probability at least 3/4 → a TM2 polynomial-time machine on (input, coin string), coins of length p(|input|), probability = exact fraction of coin strings; reason: the paper names no machine model; fair coin strings are its model (p.28)
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Lemma 4.6, p.20

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_AcceptSubcube_WCNF
import Definitions.Def_AcceptSubcube_encInst
import Definitions.Def_AcceptSubcube_coinFrac

namespace AcceptSubcube

/-- **Lemma 4.6 (Rounding of [ACMM05]).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Lemma 4.6, p.20: "There are an absolute
constant c_A and a randomized polynomial-time procedure that, given a nonnegative integer-weighted
unary/binary CNF on q variables and unit vectors v₀, . . . , v_q satisfying the squared-Euclidean
triangle inequalities on {±v₀, . . . , ±v_q}, at which the objective of (15) has value W, outputs
with probability at least 3/4 an assignment of cost at most c_A √log(q + 2) W."

**Formalization Note.** The unit vectors are given by their rational Gram matrix (`GramFeasible`:
positive semidefinite, unit diagonal, all signed triangle inequalities), `W` is (15) evaluated
through it (`objW`). Randomized polynomial time: a TM2 polynomial-time machine on (input, coin
string), coins uniform on strings of length `p(|input|)`, probability the exact fraction of coin
strings. `c_A` is chosen before everything else. The output list is read as the assignment
`x_i = Y_i`. -/
theorem lemma_4_6 :
    ∃ (cA : ℝ) (p : Polynomial ℕ)
      (alg : (ℕ × List (ℚ × List (ℕ × Bool)) × List (List ℚ)) × List Bool → List Bool),
      0 < cA ∧
      Nonempty (Turing.TM2ComputableInPolyTime encRoundCoins encAssign alg) ∧
      ∀ (q : ℕ) (Φ : WCNF) (G : List (List ℚ)),
        IsUnaryBinary Φ → NatWeights Φ → OnVars Φ (Finset.range q) → GramFeasible q G →
          (3 : ℝ) / 4 ≤
            coinFrac (p.eval (encRoundData (q, Φ, G)).length) (fun w =>
              (cnfCost Φ (fun i => (alg ((q, Φ, G), w)).getD i false) : ℝ) ≤
                cA * Real.sqrt (Real.log ((q : ℝ) + 2)) * (objW q G Φ : ℝ)) := by sorry

end AcceptSubcube
