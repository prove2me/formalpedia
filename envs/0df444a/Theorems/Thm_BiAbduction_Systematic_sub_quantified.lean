-- Prove2me | Theorems.Thm_BiAbduction_Systematic_sub_quantified
-- name    : BiAbduction.Systematic.sub_quantified
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:28.489634+00:00
-- url     : https://prove2.me/theorems/59a42c77-24b2-427a-86d9-9e1fc9c8e3e3
-- title:
--   §3.4.4 — subtraction with quantifiers: (∃X⃗.Δ) − (∃Y⃗.Δ′) is a computable disjunction of symbolic heaps
-- statement:
--   There is an algorithm that, given two symbolic heaps $\exists\vec X.\Delta$ and $\exists\vec Y.\Delta'$ of the Points-to Instantiation, where the spatial part of $\Delta$ contains no $\mathsf{true}$ conjunct ($\Delta'$ may contain one), returns a disjunction $D$ of symbolic heaps with
--   $$[\![D]\!]=(\exists\vec X.\Delta)-(\exists\vec Y.\Delta').$$
--
--   This is the binary subtraction on which the computation of $\min$ via Lemma 3.23(6) rests.
--
--   **Formalization Note** The page computes the result in the form $(\Pi''_1\wedge\Delta)\vee\dots\vee(\Pi''_j\wedge\Delta)$ under $\exists\vec X$, after an α-renaming that makes the bound variables fresh; the statement records only the semantic content (a disjunction of symbolic heaps with the same meaning) and holds without any assumption on the bound variables, since renaming them does not change the denotations. The minuend $\Delta$ is $\mathsf{true}$-free, as in the page's quantifier-free subtraction; without that restriction the claim is false ($\mathsf{true}-x\mapsto 3$ contains every state in which $x$ is unallocated, which no disjunction of symbolic heaps describes). The subtrahend may carry $\ast\,\mathsf{true}$, since $(\neg\mathsf{emp})\ast(G\ast\mathsf{true})=(\neg\mathsf{emp})\ast G$; this is the case the minimization of $D\vee\mathrm{Incompat}(\Delta)$ needs. "Algorithm" is `Computable₂` for Mathlib's standard encodings.
-- source:
--   Calcagno, Distefano, O'Hearn, Yang, Compositional Shape Analysis by means of Bi-Abduction, J. ACM (2011), pp. 33–34, §3.4.4, Subtraction with quantifiers

import Mathlib
import Definitions.Def_BiAbduction_Systematic_Syntax

namespace BiAbduction.Systematic

/-- §3.4.4, subtraction with quantifiers (pp. 33–34): for symbolic heaps `∃X⃗.Δ` and `∃Y⃗.Δ'`,
the first of whose spatial part contains no `true`, the subtraction `(∃X⃗.Δ) − (∃Y⃗.Δ')` is a
disjunction of symbolic heaps computed by an algorithm. -/
theorem sub_quantified :
    ∃ subSH : SH → SH → Disj, Computable₂ subSH ∧
      ∀ H H' : SH, H.2.2.2 = false →
        disjDen (subSH H H') = subP (shDen H) (shDen H') := by sorry

end BiAbduction.Systematic
