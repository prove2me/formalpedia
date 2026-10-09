-- Prove2me | Theorems.Thm_ErdosRenyiLSC_Main_lemma_4_3
-- name    : ErdosRenyiLSC.Main.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:01.312496+00:00
-- url     : https://prove2.me/theorems/4cfba5bb-94ee-43e5-8df7-111325ee9914
-- title:
--   Lemma 4.3, p. 34 — a priori norm bound ‖H‖ ≤ 2 + (log N)^ξ q^{−1/2}
-- statement:
--   Fix $A_0\ge10$ and $C>0$. There is $\nu>0$ such that, whenever $H$ satisfies Definition 2.1 with $\xi$ satisfying (2.4) and $q$ satisfying (2.6) (with these constants), with $(\xi,\nu)$-high probability the operator norm of $H$ on $\mathbb R^N$ with the Euclidean norm satisfies
--   $$\|H\|\le2+(\log N)^{\xi}q^{-1/2}.$$
--
--   This a priori bound places the whole spectrum of $H$ near $[-2,2]$; it is used in Section 6 to locate the eigenvalues of $A$ and in the delocalization estimates of Section 7.
--
--   **Formalization Note** $\|H\|\le c$ is written as $\|Hx\|\le c\|x\|$ for every $x\in\mathbb R^N$. $\nu$ is chosen before the random matrix, depending only on $A_0$ and $C$.
-- source:
--   Erdős, Knowles, Yau and Yin, Spectral statistics of Erdős–Rényi graphs I: Local semicircle law, arXiv:1103.1919v5, p. 34, Lemma 4.3, (4.29)

import Mathlib
import Definitions.Def_ErdosRenyiLSC_Main_Setting

noncomputable section

namespace ErdosRenyiLSC.Main

/-- Lemma 4.3, p. 34: with `(ξ, ν)`-high probability, `‖H‖ ≤ 2 + (log N)^ξ q^{-1/2}`,
where `‖H‖` is the operator norm on Euclidean space `ℝ^N`. -/
theorem lemma_4_3 :
    ∀ (A₀ C : ℝ), 10 ≤ A₀ → 0 < C →
      ∃ ν : ℝ, 0 < ν ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
          [MeasureTheory.IsProbabilityMeasure P]
          (H : (N : ℕ) → Ω → Matrix (Fin N) (Fin N) ℝ)
          (ξ q : ℕ → ℝ) (a₀ : ℝ),
          0 < a₀ → IsSparseEnsemble P H ξ q a₀ A₀ C →
          HighProb P ξ ν (fun N =>
            {ω | ∀ x : EuclideanSpace ℝ (Fin N),
              ‖Matrix.toEuclideanLin (H N ω) x‖ ≤
                (2 + Real.log (N : ℝ) ^ ξ N * q N ^ (-(1 : ℝ) / 2)) * ‖x‖}) := by sorry

end ErdosRenyiLSC.Main
