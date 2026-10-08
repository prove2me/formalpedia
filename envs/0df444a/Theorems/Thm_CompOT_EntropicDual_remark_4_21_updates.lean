-- Prove2me | Theorems.Thm_CompOT_EntropicDual_remark_4_21_updates
-- name    : CompOT.EntropicDual.remark_4_21_updates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:22.547414+00:00
-- url     : https://prove2.me/theorems/63dc4c8f-a2e3-457d-b25a-901d6059317c
-- title:
--   Remark 4.21, (4.35)–(4.36) — exact log-domain block updates
-- statement:
--   Let $a\in\Sigma_n$ and $b\in\Sigma_m$ have strictly positive entries and let $\varepsilon>0$. For any fixed $g$, the unique maximizer of $f\mapsto Q(f,g)$ is
--
--   $$
--   f_i=\varepsilon\log a_i-\varepsilon\log\left(\sum_jK_{ij}e^{g_j/\varepsilon}\right).
--   $$
--
--   Symmetrically, for fixed $f$, the unique maximizer of $g\mapsto Q(f,g)$ is
--
--   $$
--   g_j=\varepsilon\log b_j-\varepsilon\log\left(\sum_iK_{ij}e^{f_i/\varepsilon}\right).
--   $$
--
--   Alternating these exact block maximizers is the log-domain form of Sinkhorn's scaling updates.
--
--   **Formalization Note** The statement compares the dual objective with every vector in each block and characterizes equality, which gives uniqueness. Positivity makes both logarithms meaningful.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Remark 4.21, (4.35)–(4.36), p. 449. https://doi.org/10.1561/2200000073

import Mathlib
import Definitions.Def_CompOT_EntropicDual_Defs

namespace CompOT.EntropicDual

/-- Remark 4.21, (4.35)–(4.36), p. 449: each log-domain update is the
unique maximizer of the dual objective with the other potential fixed. -/
theorem remark_4_21_updates {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hε : 0 < ε)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ j, 0 < b j) :
    (∀ g f, dualObjEnt C a b ε f g ≤ dualObjEnt C a b ε (updateF C a ε g) g ∧
      (dualObjEnt C a b ε f g = dualObjEnt C a b ε (updateF C a ε g) g →
        f = updateF C a ε g)) ∧
    (∀ f g, dualObjEnt C a b ε f g ≤ dualObjEnt C a b ε f (updateG C b ε f) ∧
      (dualObjEnt C a b ε f g = dualObjEnt C a b ε f (updateG C b ε f) →
        g = updateG C b ε f)) := by sorry

end CompOT.EntropicDual
