-- Prove2me | Theorems.Thm_F3SubsetSum_exhaustive_search_circuit
-- name    : F3SubsetSum.exhaustive_search_circuit
-- status  : Proved
-- author  : @Robin Kothari
-- created : 2026-11-15T03:22:42.677198+00:00
-- url     : https://prove2.me/theorems/310e4e27-d129-4e72-a055-862d193c5baa
-- title:
--   Exhaustive search for $\mathbb F_3^n$-Subset-Sum as a uniformly generated qutrit circuit
-- statement:
--   Let $n,m\ge 0$. For an instance $h=(h_1,\dots,h_m)$ of $\mathbb F_3^n$-Subset-Sum (Problem 1.1), with each $h_i\in\mathbb F_3^n$, a solution is a nonempty set $S\subseteq[m]$ with $\sum_{i\in S}h_i=0$. Write $p_{\mathrm{sol}}(n,m)$ for the probability, over $h_1,\dots,h_m$ independent and uniform in $\mathbb F_3^n$, that a solution exists.
--
--   There are a deterministic multi-stack Turing machine $G$ (Boolean input and output alphabets) and a constant $C\in\mathbb N$ such that for all $n,m$, on input $1^n0\,1^m$ the machine $G$ halts within
--   $$C\,(n+m+2^m+1)^C$$
--   steps with the code of a qutrit circuit $\mathcal C_{n,m}$ over the gate set $G_3$ on its output stack, where:
--
--   1. $\mathcal C_{n,m}$ has at least $nm+m$ wires (the $nm$ input wires followed by the $m$ output wires);
--   2. $\mathcal C_{n,m}$ has at most $C(n+m+2^m+1)^C$ gates and at most $C(n+m+2^m+1)^C$ wires;
--   3. run on $|h\rangle\otimes|0\cdots0\rangle$ and measured in the computational basis, $\mathcal C_{n,m}$ outputs a solution of $h$ with probability at least $p_{\mathrm{sol}}(n,m)$, averaged over uniform $h$.
--
--   In words: exhaustive search over all $2^m$ subsets can be carried out by a uniformly generated qutrit circuit of size $2^{O(m)}\cdot\mathrm{poly}(n)$ that finds a solution whenever one exists. In the proof of Theorem 1.3 this handles the regime $\kappa n\le m=O(n)$, where $2^{O(m)}=(m/n)^{O(\lceil n^2/m\rceil)}$ and the success guarantee comes from Fact 1.2.
--
--   **Formalization Note** Circuits, their code `encodeCircuit`, the input layout and `successProb` are those of `F3SubsetSum.theorem_1_3`; $p_{\mathrm{sol}}$ is `probSolvable`. The runtime $C(n+m+2^m+1)^C$ is deliberately loose (any $2^{O(m)}\mathrm{poly}(n)$ suffices downstream).
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, proof of Theorem 1.3, pp.22–23 (the regime m < Kn; cf. Fact 1.2, p.4)

import Mathlib
import Definitions.Def_F3SubsetSum_SubsetSum
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_F3SubsetSum_MachineCodes
import Definitions.Def_F3SubsetSum_QutritCircuit

namespace F3SubsetSum

/-- **Exhaustive search as a circuit** (used for the regime `κn ≤ m = O(n)` of Theorem 1.3 of
Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, p.4).

There are a circuit generator `G` and a constant `C` such that for all `n`, `m`, on input
`1ⁿ 0 1ᵐ` the generator writes, within `C(n + m + 2^m + 1)^C` steps, a qutrit circuit over `G₃`
with at least `nm + m` and at most `C(n + m + 2^m + 1)^C` wires and gates that solves
Problem 1.1 on every solvable instance: its success probability is at least the probability
`probSolvable n m` that a solution exists.

Proof idea: a classical reversible circuit (gates `x`, `csum`, `ccmul` and inverses) that tries
the `2^m − 1` nonempty subsets in a fixed order, computing each subset sum into scratch wires,
testing it for zero, recording the first solution on the output wires `nm, …, nm + m − 1` under a
"found" flag, and uncomputing the scratch. On basis inputs it is a permutation, so the
measurement outputs that solution with probability `1`.

**Formalization Note** Circuits, codes and `successProb` are as in `theorem_1_3`. -/
theorem exhaustive_search_circuit :
    ∃ (G : Turing.TM2ComputableAux Bool Bool) (circ : ℕ → ℕ → Circuit) (C : ℕ),
      ∀ n m : ℕ,
        HMBinPacking.OutputsWithin G (unaryD n ++ unary m) (encodeCircuit (circ n m))
            (C * (n + m + 2 ^ m + 1) ^ C) ∧
          n * m + m ≤ (circ n m).wires ∧
          (circ n m).gates.length ≤ C * (n + m + 2 ^ m + 1) ^ C ∧
          (circ n m).wires ≤ C * (n + m + 2 ^ m + 1) ^ C ∧
          probSolvable n m ≤ successProb n m (circ n m) := by sorry

end F3SubsetSum
