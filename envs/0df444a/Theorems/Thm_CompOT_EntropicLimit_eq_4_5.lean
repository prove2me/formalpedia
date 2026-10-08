-- Prove2me | Theorems.Thm_CompOT_EntropicLimit_eq_4_5
-- name    : CompOT.EntropicLimit.eq_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:22.90707+00:00
-- url     : https://prove2.me/theorems/b51fcdbd-b42b-438f-808d-8596409aff8d
-- title:
--   (4.5), proof of Proposition 4.1, p. 426 — 0 ≤ ⟨C, P_ε⟩ − ⟨C, P⟩ ≤ ε(H(P_ε) − H(P))
-- statement:
--   Let $a$, $b$ be marginals, $C$ a cost matrix and $\varepsilon > 0$. Let $P$ be an optimal coupling of the Kantorovich problem (2.11), so $\langle C,P\rangle = L_C(a,b)$, and let $P_\varepsilon$ be an optimal solution of the entropic problem (4.2). Then
--   $$0 \le \langle C, P_\varepsilon\rangle - \langle C, P\rangle \le \varepsilon\big(\mathbf H(P_\varepsilon) - \mathbf H(P)\big).$$
--
--   This sandwich is the core estimate in the proof of Proposition 4.1: it forces limit points of $P_\varepsilon$ to be optimal and, after division by $\varepsilon$, to have maximal entropy.
--
--   **Formalization Note** The book derives (4.5) along a sequence $\varepsilon_\ell \to 0$; the inequality holds for each fixed $\varepsilon > 0$ and is stated so. No simplex hypothesis on $a,b$ is needed (the hypotheses already provide couplings).
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), proof of Proposition 4.1, eq. (4.5), p. 426

import Mathlib
import Definitions.Def_CompOT_EntropicLimit_Defs

namespace CompOT.EntropicLimit

/-- (4.5), proof of Proposition 4.1, p. 426: if `P` is optimal for (2.11) and `Q` is optimal
for (4.2) with `ε > 0`, then `0 ≤ ⟨C,Q⟩ - ⟨C,P⟩ ≤ ε (H(Q) - H(P))`. -/
theorem eq_4_5 {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ) (hε : 0 < ε)
    (P Q : Matrix (Fin n) (Fin m) ℝ)
    (hP : CompOT.Assignment.IsOptimalCoupling C a b P) (hQ : IsEntropicOptimal C a b ε Q) :
    0 ≤ CompOT.Assignment.frob C Q - CompOT.Assignment.frob C P ∧ CompOT.Assignment.frob C Q - CompOT.Assignment.frob C P ≤ ε * (entropy Q - entropy P) := by sorry

end CompOT.EntropicLimit
