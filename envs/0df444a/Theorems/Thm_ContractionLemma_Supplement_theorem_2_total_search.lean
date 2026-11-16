-- Prove2me | Theorems.Thm_ContractionLemma_Supplement_theorem_2_total_search
-- name    : ContractionLemma.Supplement.theorem_2_total_search
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:21:43.001959+00:00
-- url     : https://prove2.me/theorems/1fc8f3a1-71ee-40c6-a491-c9af19d57022
-- title:
--   Theorem 2, p.22 — total search: local Max-Cut, $\varepsilon$-Nash equilibria of graphical games and End-of-Line in time $\mathrm{poly}(L)E(n)$
-- statement:
--   The following can be computed by deterministic algorithms in time $\mathrm{poly}(L)\,E(n)$ and polynomial space, where $L$ is the input length and $E(n)=2^{O(n/\sqrt{\log n})}$:
--
--   1. **(a)** for weighted Max-Cut under single flips on an $n$-vertex graph of maximum degree $5$ with binary rational weights, a local maximum, and the number of local maxima;
--   2. **(b)** for fixed $d$ and $\varepsilon>0$, an $\varepsilon$-Nash equilibrium (with rational coordinates) of an $n$-player binary-action graphical game of degree $d$ whose payoffs are rationals in $[0,1]$, in time $\mathrm{poly}(L)\,2^{O_{d,\varepsilon}(n/\sqrt{\log n})}$;
--   3. **(c)** for every constant $c$, a solution to End-of-Line for successor and predecessor circuits with at most $c\,n$ gates in total on $n$-bit labels.
--
--   Each bound has the form $C(L+1)^C\,2^{C n/\sqrt{\log_2(n+2)}}$ in time and $C(L+1)^C$ in space, with $C$ depending only on the fixed data ($d,\varepsilon$ in (b), $c$ in (c)). All three problems are total, so these are subexponential algorithms for total search problems of the classes PLS and PPAD.
--
--   Differences from the source:
--   - reading: "This problem is PLS-complete even at degree 5 [SY91, ET11]"; "contains the PPAD-complete degree-3 polymatrix games of Rubinstein [Rub18]" → not stated; reason: cited context that the paper does not prove
--   - generalization: an $n$-vertex graph of maximum degree 5 → an edge list that may have parallel edges, degree counted with multiplicity at most 5; reason: the proof sums over edges and is unchanged; simple graphs are the special case
--   - reading: no space bound in the theorem sentence → space at most $C(L+1)^C$ (polynomial in the input length); reason: the paper's convention, p.3: "all algorithms are deterministic and use polynomial space unless we say otherwise"
--   - encoding: $O(\cdot)$, $\mathrm{poly}(\cdot)$, $E(u)=2^{O(u/\sqrt{\log u})}$ → explicit constants fixed before the instance; $E(u)=2^{C f(u)}$, $f(u)=u/\sqrt{\log_2(u+2)}$; reason: the paper's own $f$ (p.16); log base two
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem 2, p.22 (stated first on p.3); proofs pp.23–24

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Supplement_Common
import Definitions.Def_ContractionLemma_Supplement_Problems

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Theorem 2 (Total search)** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript,
sha256 049caea1…), p.22 (PDF p.25; stated first on p.3). "The following can be computed in time
`poly(L) E(n)`."

(a) A local maximum of weighted Max-Cut under single flips, on an `n`-vertex graph of maximum degree
`5` with binary rational weights, and the number of local maxima.

(b) For fixed `d` and `ε > 0`, an `ε`-Nash equilibrium of an `n`-player binary-action graphical game
of degree `d` whose payoffs are rationals in `[0, 1]`, in time `poly(L) 2^{O_{d,ε}(n/√log n)}`.

(c) A solution to End-of-Line for successor and predecessor circuits with `O(n)` gates on `n`-bit
labels.

Here `L` is the length of the instance's encoding, `poly(L) E(n)` is `C (L+1)^C 2^{C f(n)}` with
`f(n) = n/√log₂(n+2)`, and, by the paper's convention (p.3), the algorithms are deterministic and use
space `C (L+1)^C`. The constant `C` is fixed before the instance; in (b) it depends on `d` and `ε`, in
(c) on the constant `c` of `O(n)`.

**Formalization Note.** The bracketed remarks of the theorem (PLS-completeness at degree 5
[SY91, ET11]; Rubinstein's PPAD-complete polymatrix games [Rub18]) are cited context that the paper
does not prove and are not part of the statement. Max-Cut instances may have parallel edges (counted
in the degree). The equilibrium is output as a rational vector. -/
theorem theorem_2_total_search :
    (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ), ∀ H : MaxCutInst,
      (∀ v, H.deg v ≤ 5) → ∃ x : Fin H.n → Bool, H.IsLocalMax x ∧
        ContractionLemma.RunsWithin A out H.encode (vecWord x)
          (C * ((H.encode.length : ℝ) + 1) ^ C * (2 : ℝ) ^ (C * fScale H.n))
          (C * ((H.encode.length : ℝ) + 1) ^ C)) ∧
    (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ), ∀ H : MaxCutInst,
      (∀ v, H.deg v ≤ 5) →
        ContractionLemma.RunsWithin A out H.encode (countWord H.numLocalMax)
          (C * ((H.encode.length : ℝ) + 1) ^ C * (2 : ℝ) ^ (C * fScale H.n))
          (C * ((H.encode.length : ℝ) + 1) ^ C)) ∧
    (∀ (d : ℕ) (ε : ℝ), 0 < ε →
      ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ), ∀ G : GameInst,
        (∀ i, (G.nbrs i).length ≤ d) → ∃ pr : Fin G.n → ℚ, G.IsEpsNash ε (fun i => (pr i : ℝ)) ∧
          ContractionLemma.RunsWithin A out G.encode (ratVecWord pr)
            (C * ((G.encode.length : ℝ) + 1) ^ C * (2 : ℝ) ^ (C * fScale G.n))
            (C * ((G.encode.length : ℝ) + 1) ^ C)) ∧
    (∀ c : ℕ, ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ), ∀ I : EoLInst,
      I.Promise → I.gates ≤ c * I.n → ∃ x : Fin I.n → Bool, I.IsSolution x ∧
        ContractionLemma.RunsWithin A out I.encode (vecWord x)
          (C * ((I.encode.length : ℝ) + 1) ^ C * (2 : ℝ) ^ (C * fScale I.n))
          (C * ((I.encode.length : ℝ) + 1) ^ C)) := by sorry

end ContractionLemma.Supplement
