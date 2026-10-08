-- Prove2me | Theorems.Thm_CompOT_EntropicLimit_proposition_4_1
-- name    : CompOT.EntropicLimit.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:46.005904+00:00
-- url     : https://prove2.me/theorems/71c72955-9208-4a27-920b-713636ec129b
-- title:
--   Proposition 4.1, pp. 425–426 — P_ε → max-entropy optimal plan and L^ε_C → L_C as ε → 0; P_ε → a ⊗ b as ε → ∞
-- statement:
--   Let $a \in \Sigma_n$, $b \in \Sigma_m$ be histograms and $C \in \mathbb R^{n\times m}$ a cost matrix. For each $\varepsilon > 0$ let $P_\varepsilon$ be the solution of the entropic problem (4.2), and let $P^\star_0$ be the optimal coupling of the Kantorovich problem with maximal entropy (4.3). Then
--
--   1. $P_\varepsilon \to P^\star_0$ as $\varepsilon \to 0^+$;
--   2. $L^\varepsilon_C(a,b) = \langle C, P_\varepsilon\rangle - \varepsilon\mathbf H(P_\varepsilon) \to L_C(a,b) = \langle C, P^\star_0\rangle$ as $\varepsilon \to 0^+$;
--   3. $P_\varepsilon \to a\otimes b = ab^\top = (a_ib_j)_{i,j}$ as $\varepsilon \to +\infty$ (4.4).
--
--   $$P_\varepsilon \xrightarrow{\varepsilon\to 0} \operatorname*{argmin}_P\{-\mathbf H(P) : P \in U(a,b),\ \langle P,C\rangle = L_C(a,b)\},\qquad P_\varepsilon \xrightarrow{\varepsilon\to\infty} a\otimes b.$$
--
--   Small regularization recovers the most diffuse exact optimal transport plan, while large regularization yields the independent coupling.
--
--   **Formalization Note** $P_\varepsilon$ is given as any family satisfying the optimality predicate of (4.2) for each $\varepsilon > 0$ (its values at $\varepsilon \le 0$ are irrelevant), and $P^\star_0$ as any matrix satisfying the predicate of (4.3); existence and uniqueness of both are separate items of this mission, so the hypotheses are satisfiable and determine the objects. Convergence of matrices is entrywise. $\mathbf H$ uses $0\log 0 = 0$ (the book's $-\infty$ convention for zero entries is not used). Indices are 0-based.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 4.1, pp. 425–426, eqs. (4.3)–(4.4)

import Mathlib
import Definitions.Def_CompOT_EntropicLimit_Defs

namespace CompOT.EntropicLimit

open Filter Topology

/-- Proposition 4.1, pp. 425–426. Let `a ∈ Σ_n`, `b ∈ Σ_m`, `P_ε` the solution of (4.2) for
each `ε > 0`, and `P₀` the maximal-entropy optimal coupling (4.3). Then `P_ε → P₀` as
`ε → 0⁺`, `L^ε_C(a,b) = ⟨C,P_ε⟩ - ε H(P_ε) → L_C(a,b) = ⟨C,P₀⟩` as `ε → 0⁺`, and
`P_ε → a ⊗ b` as `ε → +∞` (4.4). -/
theorem proposition_4_1 {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (Pe : ℝ → Matrix (Fin n) (Fin m) ℝ)
    (hPe : ∀ ε, 0 < ε → IsEntropicOptimal C a b ε (Pe ε))
    (P₀ : Matrix (Fin n) (Fin m) ℝ) (hP₀ : IsMaxEntropyOptimal C a b P₀) :
    Tendsto Pe (𝓝[>] 0) (𝓝 P₀) ∧
      Tendsto (fun ε => entObjective C ε (Pe ε)) (𝓝[>] 0) (𝓝 (CompOT.Assignment.frob C P₀)) ∧
      Tendsto Pe atTop (𝓝 (Matrix.of fun i j => a i * b j)) := by sorry

end CompOT.EntropicLimit
