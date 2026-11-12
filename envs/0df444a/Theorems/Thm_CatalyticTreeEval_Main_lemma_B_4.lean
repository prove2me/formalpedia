-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_lemma_B_4
-- name    : CatalyticTreeEval.Main.lemma_B_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:28:25.287164+00:00
-- url     : https://prove2.me/theorems/407b0233-6b18-4149-8f87-9e1e53cf13ad
-- title:
--   Lemma B.4 — polynomial-to-vector conversion
-- statement:
--   Consider any sequence of polynomial matching systems over moduli $m>1$, indexed by supplied binary parameter strings. A system has $N$ polynomials and points, zero-free score set $S_0$, positive space scale $s$, and a finite enumeration $\mathcal M$ containing every monomial in their supports. Assume fixed finite printers produce both polynomials and points and enumerate $\mathcal M$, using at most $As$ work bits for a fixed positive $A$ throughout the sequence, and that the parameter string presented to these printers has length at most $2^{As}$.
--
--   There are one finite vector printer and a positive constant $C$, fixed before a parameter string is selected, producing an $(S_0\cup\{0\})$-matching family with
--
--   $$d=|\mathcal M|,\qquad\mathrm{space}\le C(s+\log_2m).$$
--
--   The family has size exactly $N$. In particular choosing $S_0=S_m^*\setminus\{0\}$ recovers canonical-set matching vectors. This converts the Appendix B polynomial construction into the vector interface used in the main framework.
--
--   Differences from the source:
--   - encoding: finite binary labels, tuples and printing algorithms with O/poly resource notation → Fin indices, fixed self-delimiting binary encodings and charged finite-machine runs with positive uniform constants; reason: these encode the same objects; constants precede all varying construction parameters and all runs
--   - encoding: a space-s uniform family and a space-O(s) monomial enumerator → an arbitrary parameter-indexed sequence, fixed printers and an explicit common positive multiplier A; reason: makes uniformity over the whole sequence and the allowed dependence on the supplied printers explicit; the source algorithms have a positive workspace scale
--   - reading: space-s uniformity with no stated relation between s and the printer input length → the printers' parameter string has length at most 2^(As); reason: Remark 3.8 adopts the convention that space-O(s) algorithms have inputs of length at most 2^(O(s)), and the converter must keep an O(log)-bit position in that input for a second simulated printer; every instantiation in the paper (s at least log N + δ log H + log m) satisfies it
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Lemma B.4, printed p. 37 (PDF p. 39); source.pdf SHA-256 17c3a71f0fb5afe2456558477e16fbac4200191e6e68f0facf212e24cb4ef238

import Definitions.Def_CatalyticTreeEval_Main_Polynomials

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- One finite converter handles the full parameterized sequence, not a hardcoded family. -/
theorem lemma_B_4 (P : List Bool → PolySystem) (domain : Set (List Bool))
    (MP ME : Machine) (A : ℝ) (hA : 0 < A)
    (h : ∀ a ∈ domain, (P a).valid ∧
      (((P a).params a).length : ℝ) ≤ 2 ^ (A * (P a).s) ∧
      PolyFamilyAccess MP ((P a).params a) (P a).f (P a).x (A * (P a).s) ∧
      MonomialAccess ME ((P a).params a) (P a).monomials (A * (P a).s)) :
    ∃ (MV : Machine) (C : ℝ), 0 < C ∧
      ∀ a ∈ domain,
      ∃ U V : Fin (P a).N → Vec (P a).m (P a).monomials.length,
        SMatching ((P a).S₀ ∪ {0}) U V ∧
        VectorAccess MV ((P a).params a) U V
          (C * ((P a).s + log₂ (P a).m)) := by sorry

end CatalyticTreeEval.Main
