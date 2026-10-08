-- Prove2me | Theorems.Thm_CompOT_Duality_proposition_3_2
-- name    : CompOT.Duality.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:21.817253+00:00
-- url     : https://prove2.me/theorems/0d5f08cf-8e71-4946-8fde-25b419abdf4a
-- title:
--   Proposition 3.2, p. 404 — complementary slackness: P⋆_{ij}(C_{ij} − f⋆_i − g⋆_j) = 0
-- statement:
--   Let $a \in \Sigma_n$, $b \in \Sigma_m$ be histograms and $C \in \mathbb R^{n\times m}$. Let $P^\star$ be an optimal solution of the primal problem (2.11) and $(f^\star, g^\star)$ an optimal solution of the dual problem (2.20). Then for every $(i,j) \in \llbracket n\rrbracket\times\llbracket m\rrbracket$:
--
--   1. $P^\star_{i,j}\,(C_{i,j} - f^\star_i - g^\star_j) = 0$;
--   2. if $P^\star_{i,j} > 0$ then $f^\star_i + g^\star_j = C_{i,j}$;
--   3. if $f^\star_i + g^\star_j < C_{i,j}$ then $P^\star_{i,j} = 0$.
--
--   Equivalently, the support of an optimal plan lies in the set where the optimal potentials are tight, as in (2.23).
--
--   **Formalization Note** The printed product reads $P^\star_{i,j}(C_{i,j} - f^\star_i + g^\star_j)$; the proof on p. 404 and the "in other words" sentence both use $C - f^\star\oplus g^\star$, so the intended sign $-g^\star_j$ is stated. The page also labels the primal and dual "(2.24)" and "(2.11)"; the discrete primal (2.11) and dual (2.20) are meant.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 3.2, p. 404 (cf. (2.23), p. 383)

import Mathlib
import Definitions.Def_CompOT_Duality_Defs

namespace CompOT.Duality

/-- Proposition 3.2, p. 404 (complementary slackness), with the printed sign slip corrected:
if `P⋆` is optimal for the primal (2.11) and `(f⋆, g⋆)` is optimal for the dual (2.20), then for
every `(i, j)`: `P⋆_{ij} (C_{ij} − f⋆_i − g⋆_j) = 0`; if `P⋆_{ij} > 0` then `f⋆_i + g⋆_j = C_{ij}`;
and if `f⋆_i + g⋆_j < C_{ij}` then `P⋆_{ij} = 0`. -/
theorem proposition_3_2 {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (C P : Matrix (Fin n) (Fin m) ℝ) (hP : CompOT.Assignment.IsOptimalCoupling C a b P)
    (f : Fin n → ℝ) (g : Fin m → ℝ) (hfg : IsDualOptimal C a b f g) :
    ∀ i j, P i j * (C i j - f i - g j) = 0 ∧
      (0 < P i j → f i + g j = C i j) ∧ (f i + g j < C i j → P i j = 0) := by sorry

end CompOT.Duality
