-- Prove2me | Theorems.Thm_BipColorHard_proposition_8
-- name    : BipColorHard.proposition_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:25.642571+00:00
-- url     : https://prove2.me/theorems/e2c24bfd-5f71-463d-b334-aa69ffdd802c
-- title:
--   Proposition 8 — gap MAX-CUT reduces to bipartite phase labeling
-- statement:
--   Let $q=2k+1\ge3$ and let $g>0$ be rational. For every fixed $u\in(0,1/k)$, there are an integer $D_0\ge1$ and a constant $\eta>0$ such that the following holds. A polynomial-time algorithm that approximates $Z_{W_u}(H)$ within a factor $e^{\eta|V(H)|}$ on bipartite multigraphs $H$ of maximum degree at most $D_0$ yields a polynomial-time algorithm for gap MAX-CUT, the problem of deciding, for a graph $F$ of maximum degree at most three and an integer $\tau$, which of
--   $$\mathrm{MaxCut}(F)\le\tau\quad\text{and}\quad\mathrm{MaxCut}(F)\ge\tau+g|V(F)|$$
--   holds, under the promise that one does.
--
--   Precisely, there are a polynomial-time instance map into instances of maximum degree at most $D_0$ and a polynomial-time answer map such that every rational within $e^{\pm\eta|V(H)|}$ of $Z_{W_u}(H)$ lets the answer map decide the case.
--
--   This is the first reduction of the proof of Theorem 1.
--
--   Differences from the source:
--   - generalization: $g$ the constant of Theorem 6 → every rational $g>0$; reason: the proof uses only $g>0$, through (16), so this specializes to the source
--   - reading: "a polynomial-time algorithm ... yields a polynomial-time algorithm" → one query to the approximation, post-processed, correct for every admissible rational answer; reason: §4.4 builds exactly this reduction
--   - reading: the two promise cases → each clause assumes the other case fails; reason: the cases coincide only on the empty graph with $\tau=0$, where either answer says which holds
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Proposition 8, p.7 (PDF p.9); §4, p.14 (PDF p.16); §4.4, pp.19–20 (PDF pp.21–22)

import Definitions.Def_BipColorHard_Hardness
import Definitions.Def_BipColorHard_PhaseLabeling
import Definitions.Def_IIDMatchHard_Cut

set_option autoImplicit false

namespace BipColorHard

open NSWApxHard.Reduction (GraphInput) in
/-- **Proposition 8**, p.7 (PDF p.9), manuscript sha256 78a66d1f…, for `q = 2k + 1 ≥ 3`. For every fixed `u ∈ (0, 1/k)`, there are an integer `D₀ ≥ 1` and a constant `η > 0` such
that the following holds. A polynomial-time algorithm that approximates `Z_{W_u}(H)` within a factor `e^{η|V(H)|}` on bipartite multigraphs `H` of maximum degree at most `D₀`
yields a polynomial-time algorithm for gap MAX-CUT.

**Formalization Note.** "Yields" is a reduction with one query, as in §4.4: an instance map `f`, computed on encodings by the polynomial-time `fs`, and a polynomial-time answer map
`a`, correct for every admissible rational answer. It handles every instance of Theorem 6: any integer `τ`, any graph of maximum degree at most three, isolated vertices allowed
("the remaining cases are decided directly", p.14, PDF p.16). The two promise cases of gap MAX-CUT are exclusive except when `F` has no vertices and `τ = 0`, where either answer
decides "which holds"; so each clause assumes that the other case fails. The manuscript fixes `g` from Theorem 6; the statement holds for every `g > 0`. -/
theorem proposition_8 (k : ℕ) (hk : 1 ≤ k) (g : ℚ) (hg : 0 < g) (u : ℝ) (hu0 : 0 < u)
    (hu1 : u < 1 / (k : ℝ)) :
    ∃ D0 : ℕ, 1 ≤ D0 ∧ ∃ η : ℝ, 0 < η ∧
      ∃ (f : GraphInput × ℤ → PhaseInst) (fs : List Bool → List Bool)
        (a : List (Option (Bool ⊕ Bool)) → List Bool),
        CookPvsNP.PolyTimeComputable fs ∧ CookPvsNP.PolyTimeComputable a ∧
        ∀ (F : GraphInput) (τ : ℤ), MaxDegLe 3 F →
          fs (encGap (F, τ)) = encPhase (f (F, τ)) ∧
          (f (F, τ)).DegLe D0 ∧
          ∀ r : ℚ, WithinExp (η * (((f (F, τ)).nL : ℝ) + ((f (F, τ)).nR : ℝ))) (phaseZ k u (f (F, τ))) r →
            (((IIDMatchHard.maxCut F.G : ℝ) ≤ (τ : ℝ) ∧
                ¬ (τ : ℝ) + (g : ℝ) * (F.N : ℝ) ≤ (IIDMatchHard.maxCut F.G : ℝ)) →
              a (IIDMatchHard.pairInput (encGap (F, τ)) r) ≠ [true]) ∧
            (((τ : ℝ) + (g : ℝ) * (F.N : ℝ) ≤ (IIDMatchHard.maxCut F.G : ℝ) ∧
                ¬ (IIDMatchHard.maxCut F.G : ℝ) ≤ (τ : ℝ)) →
              a (IIDMatchHard.pairInput (encGap (F, τ)) r) = [true]) := by sorry

end BipColorHard
