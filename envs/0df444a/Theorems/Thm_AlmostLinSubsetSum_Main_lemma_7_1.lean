-- Prove2me | Theorems.Thm_AlmostLinSubsetSum_Main_lemma_7_1
-- name    : AlmostLinSubsetSum.Main.lemma_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:29:05.329099+00:00
-- url     : https://prove2.me/theorems/027704d7-fa85-4a48-a214-442f2e68f305
-- title:
--   Lemma 7.1 — comparison of repeated vector sumsets: $|kS|=O_{d,\varepsilon}(|\lfloor k/2\rfloor S|)$
-- statement:
--   **Lemma 7.1** (p. 34). If $S\subseteq Q_0\cap\mathbb Z^d$ contains $0$, then $|kS|=O_{d,\varepsilon}(|\lfloor k/2\rfloor S|)$.
--
--   Setting of §7.1–7.2: $Q_0=\prod_j[-N_j,N_j]$ with integers $N_j\ge1$, $W:=|Q_0|=\prod_j(2N_j+1)$, $0<\varepsilon\le1/(2d)$, $k:=\lfloor W^{\varepsilon/3}\rfloor$, and the standing assumption $W\ge W_{\min}(d,\varepsilon)$.
--
--   Formally: for every $d\ge1$ and real $\varepsilon\in(0,1/(2d)]$ there are $C>0$ and $W_{\min}$ such that for all $N_j\ge1$ with $W\ge W_{\min}$ and every $S\subseteq Q_0\cap\mathbb Z^d$ with $0\in S$, $|kS|\le C\,|\lfloor k/2\rfloor S|$ ($kS$ the $k$-fold sumset).
--
--   Differences from the source:
--   - generalization: ε rational with 0 < ε ≤ 1/(2d) (§3, §7.1) → ε real with 0 < ε ≤ 1/(2d); reason: rationality is used only to compute ⌊W^{ε/3}⌋ exactly in the algorithm, not in this lemma; rational ε are a special case
--   - reading: O_{d,ε}(·) under the standing assumption W ≥ W_min(d, ε) → ∃ C > 0 and W_min, depending on d and ε only, chosen before N and S; reason: explicit form of the constant and the threshold
-- source:
--   Chen, Mao, Zhang (2026), An Almost-Linear Time Algorithm for Multidimensional Subset Sum, STOC 2027 submission, SHA-256 0cd42ca048cfff088013ad06450a278a6df72a29004c48c5c138f3f6df85d1e0, Lemma 7.1, p. 34 (setting p. 34, (35))

import Mathlib
import Definitions.Def_AlmostLinSubsetSum_Main_Basic

set_option autoImplicit false

namespace AlmostLinSubsetSum.Main

/-- **Lemma 7.1** (Comparison of repeated vector sumsets; Chen, Mao, Zhang 2026, p. 34). If
`S ⊆ Q₀ ∩ ℤ^d` contains `0`, then `|kS| = O_{d,ε}(|⌊k/2⌋S|)`.

Setting of §7.1–7.2: `Q₀ = ∏_j [−N_j, N_j]` with integers `N_j ≥ 1`,
`W := |Q₀| = ∏_j (2N_j + 1)`, `0 < ε ≤ 1/(2d)`, `k := ⌊W^{ε/3}⌋`, and the standing assumption
`W ≥ W_min(d, ε)`; `kS` is the `k`-fold sumset. The constant `C` and the threshold `W_min`
depend only on `d` and `ε`. -/
theorem lemma_7_1 :
    ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (2 * d) →
    ∃ C : ℝ, 0 < C ∧ ∃ Wmin : ℕ,
    ∀ N : Fin d → ℕ, (∀ j, 1 ≤ N j) → Wmin ≤ ∏ j, (2 * N j + 1) →
    ∀ S : Set (Fin d → ℤ), (∀ x ∈ S, ∀ j, |x j| ≤ (N j : ℤ)) → (0 : Fin d → ℤ) ∈ S →
      ((kFold ⌊((∏ j, (2 * N j + 1) : ℕ) : ℝ) ^ (ε / 3)⌋₊ S).ncard : ℝ) ≤
        C * (kFold (⌊((∏ j, (2 * N j + 1) : ℕ) : ℝ) ^ (ε / 3)⌋₊ / 2) S).ncard := by sorry

end AlmostLinSubsetSum.Main
