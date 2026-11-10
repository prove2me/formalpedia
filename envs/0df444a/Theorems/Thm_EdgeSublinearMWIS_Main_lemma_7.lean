-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_lemma_7
-- name    : EdgeSublinearMWIS.Main.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:42:02.597655+00:00
-- url     : https://prove2.me/theorems/0eaabe0e-f91e-4509-b544-6185defd09e4
-- title:
--   Lemma 7 — algorithmic vertex flow–cut alternative
-- statement:
--   For $n\ge2$, a graph $G$, nonnegative rational vertex costs $x$ and rational $\gamma>0$, a single deterministic program runs in polynomial input-bit time. It returns either a unit all-pairs flow $f$ with $\operatorname{load}_f(v)\le\gamma x_v$ at every vertex, or a nonempty-sided overlapping separation $(A,B)$ satisfying
--   $$x(A\cap B)\le K|A||B|\log_2(n)/\gamma.$$
--   The positive constant $K$ is absolute. Every ordered pair, including diagonal pairs, has demand one, and path loads include endpoints. The rational positive-support path representation is part of the output and its length is charged. This is the vertex-load algorithmic form needed by the separator routine.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graphs → graphs labeled by Fin n and finite vertex masks; reason: every finite graph admits such a labeling; induced injections transport class membership
--   - encoding: a deterministic polynomial-time algorithm on rational inputs → one finite program, serialized rational inputs and actual halting-step bounds; reason: binary conventions fix a computational model without restricting rational values
--   - encoding: O(|A||B| log n/gamma) → an absolute positive constant before every input; reason: the source leaves its numerical value unspecified
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Lemma 7, p.7 (PDF p.7), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Paths

namespace EdgeSublinearMWIS.Main

theorem lemma_7 :
    ∃ (M : Program) (K : ℝ) (time : Polynomial ℕ), 0 < K ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (x : Fin n → RationalCode) (γ : RationalCode),
        2 ≤ n → (∀ v, 0 ≤ (x v).value) → 0 < γ.value →
        ∃ t : ℕ, t ≤ time.eval ((flowInput G x γ).length + 1) ∧
          ((∃ f : List (List (Fin n) × ℚ),
              Runs M (flowInput G x γ) (false :: encodeSparsePaths f) t ∧ UnitFlow G f ∧
              ∀ v, vertexMass (realPaths f) v ≤ (γ.value : ℝ) * ((x v).value : ℝ)) ∨
            ∃ A B : Finset (Fin n),
              Runs M (flowInput G x γ) (true :: (mask A ++ mask B)) t ∧ Separation G A B ∧
              vertexSum (fun v => ((x v).value : ℝ)) (A ∩ B) ≤
                K * A.card * B.card * logTwo n / (γ.value : ℝ)) := by sorry

end EdgeSublinearMWIS.Main
