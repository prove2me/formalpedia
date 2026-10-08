-- Prove2me | Theorems.Thm_CompOT_EntropicLimit_max_entropy_optimal_exists_unique
-- name    : CompOT.EntropicLimit.max_entropy_optimal_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:48.099112+00:00
-- url     : https://prove2.me/theorems/7696f71e-140b-4f92-8939-60b050e62fc9
-- title:
--   Proof of Proposition 4.1, p. 426 — the maximum-entropy optimal coupling (4.3) exists and is unique
-- statement:
--   Let $a \in \Sigma_n$, $b \in \Sigma_m$ and $C \in \mathbb R^{n\times m}$. Among the optimal couplings of the Kantorovich problem, i.e. the $P \in U(a,b)$ with $\langle C, P\rangle = L_C(a,b)$, there is exactly one of maximal entropy:
--   $$\operatorname*{argmin}_P \{-\mathbf H(P) : P \in U(a,b),\ \langle P, C\rangle = L_C(a,b)\}$$
--   is a single matrix $P^\star_0$.
--
--   This is the limit object of Proposition 4.1 as $\varepsilon \to 0$; its uniqueness is what lets the whole family $P_\varepsilon$ converge rather than only a subsequence.
--
--   **Formalization Note** $\mathbf H$ uses $0\log 0 = 0$, so optimal couplings with zero entries are admissible; indices are 0-based.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), (4.3), p. 426, and proof of Proposition 4.1, p. 426

import Mathlib
import Definitions.Def_CompOT_EntropicLimit_Defs

namespace CompOT.EntropicLimit

/-- Proof of Proposition 4.1, p. 426: for `a ∈ Σ_n`, `b ∈ Σ_m`, program (4.3) (maximize the
entropy over the optimal couplings of (2.11)) has a solution, and it is unique. -/
theorem max_entropy_optimal_exists_unique {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    ∃! P : Matrix (Fin n) (Fin m) ℝ, IsMaxEntropyOptimal C a b P := by sorry

end CompOT.EntropicLimit
