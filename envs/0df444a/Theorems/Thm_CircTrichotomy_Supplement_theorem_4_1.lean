-- Prove2me | Theorems.Thm_CircTrichotomy_Supplement_theorem_4_1
-- name    : CircTrichotomy.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:14:48.228107+00:00
-- url     : https://prove2.me/theorems/31ed5bd8-3dfc-46c9-a710-a42cad5e3f14
-- title:
--   Theorem 4.1 — deciding, for an NFA, almost logarithmic or linear circuit complexity is PSPACE-complete
-- statement:
--   For a regular language $L\subseteq\Sigma^+$ write $c(L)$ for its circuit complexity. By Theorem 2.1, $L$ has exactly one of: constant circuit complexity $c(L)\in O(1)$; **almost logarithmic** circuit complexity $c(L)\in\Omega(\log n)\cap O(\log n\log\log n)$; **linear** circuit complexity $c(L)\in\Omega(n)\cap O(n)$ (Hardy–Littlewood $\Omega$).
--
--   **Theorem 4.1.** Let $\mathcal C$ be either the class of regular languages of almost logarithmic circuit complexity or the class of regular languages of linear circuit complexity. The problem
--
--   > given a nondeterministic finite automaton $A$ (with its alphabet), decide whether $L(A)\in\mathcal C$
--
--   is PSPACE-complete under logarithmic-space many-one reductions. Both classes are asserted: each of the two problems is in PSPACE, and each is PSPACE-hard.
--
--   The theorem makes the trichotomy effective: the class of a regular language given by an NFA can be computed in polynomial space, and no algorithm does essentially better unless PSPACE collapses. Together with the corresponding result for the constant class ([GM26b], Theorem 5.1) it covers all three cases.
--
--   **Formalization Note** An NFA is given by the bit string `NFAInst.enc A`; the problem is the set of codes of NFAs whose language is in $\mathcal C$. PSPACE and log-space computability are those of the published machine model `ArrighiStarFree.HalfLevel.SpaceMachine`.
--
--   Differences from the source:
--   - encoding: an NFA A = (Q, Σ, ∆, q0, F) given as input; no encoding is fixed → NFAInst with Q = Fin (numStates + 1), Σ = Fin (numLetters + 1), ∆ and F as lists, written as the bit string NFAInst.enc (sizes in unary, indices in self-delimiting binary); strings that encode no NFA are not in the problem; reason: a standard reasonable encoding: its length is at least |A| and polynomial in the instance, and it is decoded in logarithmic space; NFAs with an empty alphabet (L(A) = ∅, in neither class) have no code, which removes only no-instances
--   - encoding: PSPACE; deciding if L is in C → InPSPACE and PSPACEHardLog in the published SpaceMachine model, for the language of codes membershipProblem P; reason: the paper fixes no machine model; deterministic polynomial space equals the paper's nondeterministic polynomial space (Savitch)
--   - encoding: C the class of regular languages of almost logarithmic, resp. linear, circuit complexity as stated by Theorem 2.1 → IsAlmostLog / IsLinearCC: clauses (2) and (3) of the published theorem_2_1, with HLOmega, BigO and Real.logb 2, for L(A) over the NFA's own alphabet; reason: these are the clauses of Theorem 2.1 verbatim; L(A) is regular, so the restriction to regular languages is automatic
--   - reading: PSPACE-complete → PSPACE-complete under deterministic logarithmic-space many-one reductions; reason: Proposition F.6 (p.70) and §7 (p.13) state hardness under logarithmic-space reductions; this is the stronger reading (polynomial-time reductions would be weaker)
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 4.1, p.10 (restated p.67; same statement as Theorem F.3, p.68); Problem F.1, p.67; Propositions F.5, F.6, pp.69–70

import Mathlib
import Definitions.Def_CircTrichotomy_Supplement_InPSPACE
import Definitions.Def_CircTrichotomy_Supplement_membershipProblem

set_option autoImplicit false

namespace CircTrichotomy

namespace Supplement

/-- **Theorem 4.1** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*,
arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 4.1, p.10; restated
p.67; the same statement as Theorem F.3, p.68): "Whenever C is either the class of regular
languages of almost logarithmic or linear circuit complexity as stated by Theorem 2.1, given a
nondeterministic finite automaton recognizing a regular language L, deciding if L is in C is
PSPACE-complete."

Both membership problems are PSPACE-complete under logarithmic-space many-one reductions: the set
of codes of NFAs `A` with `c(L(A)) ∈ Ω(log n) ∩ O(log n log log n)`, and the set of codes of NFAs
`A` with `c(L(A)) ∈ Ω(n) ∩ O(n)` (Hardy–Littlewood `Ω`).

**Formalization Note**
* The classes are clauses (2) and (3) of the published `theorem_2_1` (`IsAlmostLog`,
  `IsLinearCC`), for `L(A) ⊆ Σ⁺` over the instance's own alphabet `Fin (numLetters + 1)`.
* An NFA is given by the binary code `NFAInst.enc` (sizes in unary, indices in self-delimiting
  binary); strings that encode no NFA are not in either language.
* PSPACE and the log-space reductions are in the published `SpaceMachine` model; the reductions
  are log-space as in Proposition F.6 (p.70) and §7 (p.13). -/
theorem theorem_4_1 :
    PSPACECompleteLog (membershipProblem fun _ L => IsAlmostLog L) ∧
      PSPACECompleteLog (membershipProblem fun _ L => IsLinearCC L) := by sorry

end Supplement

end CircTrichotomy
