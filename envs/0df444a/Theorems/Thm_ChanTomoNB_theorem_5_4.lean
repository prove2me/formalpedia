-- Prove2me | Theorems.Thm_ChanTomoNB_theorem_5_4
-- name    : ChanTomoNB.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:30:30.665746+00:00
-- url     : https://prove2.me/theorems/3c4d67e4-0ce9-43dd-8b2a-e9c2d3fa00c2
-- title:
--   Theorem 5.4 — packing net $\mathcal N\subseteq\mathcal G$ with $|\mathcal N|\ge\frac12(1/\eta)^{2\alpha d'}$ and uniform Choi and diamond separations
-- statement:
--   In the near-boundary regime ($d_2\ge2$, $r\ge1$, $d_1<rd_2<2d_1$), let $F$ be a balanced reference and $P\mapsto W_P$ a choice of isometries, and put $\mathcal O_P=\{\mathcal E_{P,U}:U\in\mathbb U_{d'}\}$. For each $0<\eta<1$ there is a finite $\mathcal N\subseteq\mathcal G$ such that
--   $$
--   |\mathcal N|\ge\frac12\Big(\frac1\eta\Big)^{2\alpha d'},\qquad \|P-Q\|_1>\frac{4\alpha d'}{e(d'+\alpha)}\eta\quad(P\ne Q\in\mathcal N),
--   $$
--   and for distinct $P,Q\in\mathcal N$
--   $$
--   \inf_{\mathcal E\in\mathcal O_P,\mathcal F\in\mathcal O_Q}\frac1{d_1}\|C_{\mathcal E}-C_{\mathcal F}\|_1>\frac{\sqrt\chi}{3e\sqrt{C_0}\,d_1}\eta,\qquad \inf_{\mathcal E\in\mathcal O_P,\mathcal F\in\mathcal O_Q}\|\mathcal E-\mathcal F\|_\diamond>\frac{\eta}{e\sqrt8}.
--   $$
--
--   This packing net reduces tomography to the discrimination problem of Theorem 4.2.
--
--   Differences from the source:
--   - encoding: standing assumptions of §5: d2 ≥ 2 (p.10, "throughout"), r ≥ 1 and d1 < rd2 < 2d1 (p.24, "This construction applies throughout the near-boundary regime") → explicit hypotheses 2 ≤ d2, 1 ≤ r, d1 < r·d2, r·d2 < 2·d1; reason: the result is stated under the section's standing assumptions
--   - generalization: "Fix such an isometry F", "fix an isometry W_P", "a fixed projector" (pp.25–26) → every isometry F with tr_B(FF†) ⪰ λ0 I_r, every choice P ↦ W_P with W_P†W_P = I and W_P W_P† = P, and (for µ) every isometry Ψ onto im Π; reason: the statement holds for every admissible choice and specializes to the paper's fixed ones
--   - encoding: ‖E − F‖_⋄ = max over density operators ρ_AR, H_R ≅ C^{d1} (p.10) → sSup of the same set of values ‖((E − F) ⊗ I_R)(ρ)‖_1, H_R ≅ C^{d1}; reason: the set is nonempty and bounded, so the supremum is the printed maximum
--   - encoding: inf over E ∈ O_P, F ∈ O_Q → ⨅ over U ∈ U(d′) and U′ ∈ U(d′) of the distance between E_{P,U} and E_{Q,U′} (a real infimum of a set bounded below by 0); reason: the same infimum
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, Theorem 5.4, Eqs. (54)–(56), p.27

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_ChanTomoNB_choiDist
import Definitions.Def_ChanTomoNB_diamondDist
import Definitions.Def_ChanTomoNB_matrixNorms
import Definitions.Def_ChanTomoNB_hardChannel

open Matrix MeasureTheory
open scoped ComplexOrder

namespace ChanTomoNB

/-- **Theorem 5.4 (Existence of packing net).** Chen, Oufkir, *Quantum channel tomography: optimal
bounds in the near-boundary regime*, arXiv:2611.03639v1, Theorem 5.4, Eqs. (54)–(56), p.27: "For
each 0 < η < 1, there is a finite N ⊆ G such that |N| ≥ (1/2)(1/η)^{2αd′},
‖P − Q‖_1 > (4αd′/(e(d′ + α)))η (P ≠ Q ∈ N). Let O_P = {E_{P,U} : U ∈ U_{d′}}. For distinct
P, Q ∈ N, the separation holds uniformly:
inf_{E∈O_P, F∈O_Q} (1/d1)‖C_E − C_F‖_1 > (√χ/(3e√C0 d1))η,
inf_{E∈O_P, F∈O_Q} ‖E − F‖_⋄ > η/(e√8)."

**Formalization Note.** The infima over `O_P × O_Q` are `⨅ U ⨅ U′` over the unitary group
`U(d′)`, real infima of sets bounded below by `0`; the separations are strict inequalities on
the infima, as printed. `C₀ = 450`. The balanced reference `F` and the choice `W` are arbitrary
admissible ones (Reading 7). -/
theorem theorem_5_4 (d1 d2 r : ℕ) (hd2 : 2 ≤ d2) (hr : 1 ≤ r) (hlo : d1 < r * d2)
    (hhi : r * d2 < 2 * d1)
    (F : Matrix (Fin d2 × Fin r) (Fin (d1 - dp d1)) ℂ) (hF : IsBalancedRef d1 d2 r F)
    (W : Matrix (Fin d2 × Fin r) (Fin d2 × Fin r) ℂ → Matrix (Fin d2 × Fin r) (Fin (dp d1)) ℂ)
    (hW : IsSignalChoice (d1 := d1) F W) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ N : Finset (Matrix (Fin d2 × Fin r) (Fin d2 × Fin r) ℂ),
      (∀ P ∈ N, P ∈ goodSet (d1 := d1) F) ∧
      1 / 2 * (1 / η) ^ (2 * alpha d1 d2 r * dp d1) ≤ (N.card : ℝ) ∧
      ∀ P ∈ N, ∀ Q ∈ N, P ≠ Q →
        4 * (alpha d1 d2 r : ℝ) * dp d1 / (Real.exp 1 * ((dp d1 : ℝ) + alpha d1 d2 r)) * η <
            WildeQIT.traceNorm (P - Q) ∧
          Real.sqrt (chi d1 d2 r) / (3 * Real.exp 1 * Real.sqrt C0 * d1) * η <
            ⨅ U : Matrix.unitaryGroup (Fin (dp d1)) ℂ, ⨅ U' : Matrix.unitaryGroup (Fin (dp d1)) ℂ,
              choiDist (E5 (d1 := d1) F (W P) (U : Matrix (Fin (dp d1)) (Fin (dp d1)) ℂ))
                (E5 (d1 := d1) F (W Q) (U' : Matrix (Fin (dp d1)) (Fin (dp d1)) ℂ)) ∧
          η / (Real.exp 1 * Real.sqrt 8) <
            ⨅ U : Matrix.unitaryGroup (Fin (dp d1)) ℂ, ⨅ U' : Matrix.unitaryGroup (Fin (dp d1)) ℂ,
              diamondDist (E5 (d1 := d1) F (W P) (U : Matrix (Fin (dp d1)) (Fin (dp d1)) ℂ))
                (E5 (d1 := d1) F (W Q) (U' : Matrix (Fin (dp d1)) (Fin (dp d1)) ℂ)) := by sorry

end ChanTomoNB
