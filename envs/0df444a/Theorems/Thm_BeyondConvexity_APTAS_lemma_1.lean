-- Prove2me | Theorems.Thm_BeyondConvexity_APTAS_lemma_1
-- name    : BeyondConvexity.APTAS.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:13:24.878064+00:00
-- url     : https://prove2.me/theorems/8c7998e4-a0aa-42aa-b333-1e252bce93c5
-- title:
--   Lemma 1 — exact local packing with rational output
-- statement:
--   Let $P_1,\ldots,P_k$ be valid rational polygonal regions and let $Q$ be a valid rational polygonal container, all allowing holes. Write $L_{\rm loc}\ge2$ for their total binary encoding length. There is one algorithm that decides feasibility under real translations in time
--
--   $$F_{\rm loc}(k)L_{\rm loc}^{c(k+1)},$$
--
--   where $c$ is an absolute integer constant and $F_{\rm loc}$ is computable and nondecreasing. Its answer is negative precisely when no real translational packing exists. A positive answer returns rational translations giving a feasible packing, with total output encoding length at most $CL_{\rm loc}^{d}$ for absolute constants $C,d$.
--
--   All boundary vertices remain part of the input. There are no convexity, rotation, unit-container, rasterizability, or representative-roundability hypotheses. This is the exact finite-query result used for containment and local configurations.
--
--   Differences from the source:
--   - encoding: decide feasibility and compute rational translations in F_loc(k)L_loc^{O(k+1)} time → one finite-alphabet TM2 machine with a joint optional rational-list output and explicit absolute exponent constant c; reason: machine execution binds the decision and witness to the same computation; explicit c expands the big-O notation
--   - encoding: labeled objects, polygonal container, binary length and polynomial-size rational translations → lists of boundary-cycle records, fixed binary encoders, and a bound C L_loc^d on the whole output code; reason: list positions preserve labels; the rational-linear-algebra proof gives a uniform polynomial bit bound
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/890.pdf, Lemma 1 and its complete proof, printed p.8 / PDF p.9; uniform output-bit use in Appendix D.9, printed p.33 / PDF p.34.

import Definitions.Def_BeyondConvexity_APTAS_PolynomialOn

namespace BeyondConvexity.APTAS

open RSListDecodingCapacity.AllRates (encNat encList)

/-- Silva, Dell'Arriva, Miyazawa, STOC 2027 submission #890 (October 2026),
Lemma 1, printed p.8 / PDF p.9. The same machine decides real feasibility and,
on a yes instance, outputs the rational realization. No uniform geometric class
hypotheses, convexity, bounded boundary complexity, or unit-container restriction. -/
theorem lemma_1 :
    ∃ (M : BitMachine) (F : ℕ → ℕ) (c C d : ℕ),
      M.Finite ∧ Effective encNat encNat F ∧ Monotone F ∧
      ∀ (I : Instance) (Q : Polygon),
        (∀ p ∈ I, p.Valid) → Q.Valid →
        ∃ out : Option (List QPoint),
          M.Runs (encInstance I ++ encPolygon Q)
            (match out with
             | none => [false]
             | some v => true :: encList encPoint v)
            (F I.length *
              (max 2 (encInstance I ++ encPolygon Q).length)^(c * (I.length + 1))) ∧
          (out = none ↔ ¬ ∃ v : List Point, LocalFeasible I Q v) ∧
          (∀ v, out = some v →
            LocalFeasible I Q (v.map QPoint.real) ∧
              (encList encPoint v).length ≤
                C * (max 2 (encInstance I ++ encPolygon Q).length)^d) := by sorry

end BeyondConvexity.APTAS
