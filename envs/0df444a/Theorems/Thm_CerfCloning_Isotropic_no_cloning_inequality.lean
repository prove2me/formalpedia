-- Prove2me | Theorems.Thm_CerfCloning_Isotropic_no_cloning_inequality
-- name    : CerfCloning.Isotropic.no_cloning_inequality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:29:48.160979+00:00
-- url     : https://prove2.me/theorems/d52a967c-80e1-45bd-ab46-e368a228ee8d
-- title:
--   Eq. (1.1) = (3.21), pp. 2, 15 — every isotropic cloner obeys $\pi_a + \frac2N\sqrt{\pi_a\pi_b} + \pi_b \ge 1$, and every point of the ellipse is attained
-- statement:
--   Let $N \ge 2$. A $1 \to 2$ **isotropic cloner** of an $N$-level system with **depolarizing fractions** $\pi_a, \pi_b \in \mathbb R$ is a quantum channel $T$ (completely positive and trace preserving) from operators on the $N$-level input to operators on $A \otimes B$, two $N$-level outputs, whose two outputs emerge from depolarizing channels: for every operator $\rho$,
--   $$\operatorname{Tr}_B T(\rho) = \frac{\pi_a}{N}(\operatorname{Tr}\rho)\,\mathbb 1 + (1-\pi_a)\,\rho, \qquad \operatorname{Tr}_A T(\rho) = \frac{\pi_b}{N}(\operatorname{Tr}\rho)\,\mathbb 1 + (1-\pi_b)\,\rho ,$$
--   i.e. copy $A$ is the input replaced by a random state with probability $\pi_a$, and copy $B$ with probability $\pi_b$. Write $a = \sqrt{\pi_a}$ and $b = \sqrt{\pi_b}$.
--
--   1. **No-cloning inequality.** Every isotropic cloner satisfies
--   $$a^2 + \frac{2}{N}\, ab + b^2 \;=\; \pi_a + \frac{2}{N}\sqrt{\pi_a}\sqrt{\pi_b} + \pi_b \;\ge\; 1 .$$
--   2. **Tightness.** For all $\pi_a, \pi_b \ge 0$ with $\pi_a + \frac2N\sqrt{\pi_a}\sqrt{\pi_b} + \pi_b = 1$ there is an isotropic cloner with depolarizing fractions $\pi_a$ and $\pi_b$.
--
--   So the region of $(\sqrt{\pi_a}, \sqrt{\pi_b})$ inside the ellipse $a^2 + \frac2N ab + b^2 = 1$, which would represent close-to-perfect cloning, is forbidden by quantum mechanics, and the ellipse itself is the exact boundary of what isotropic cloners achieve (the paper attains it with isotropic Heisenberg cloning machines). For $N = 2$ this is the qubit no-cloning inequality; as $N \to \infty$ the ellipse tends to the line $\pi_a + \pi_b = 1$.
--
--   **Formalization Note** A channel is a finite family of Kraus operators $K_i$ with $\sum_i K_i^\dagger K_i = \mathbb 1$ (`QAlgorithms.IsChannel`), which in finite dimension is exactly a completely positive trace-preserving map. The first factor of the output space is $A$. The output conditions are imposed on every matrix $\rho$; for a linear map that is the same as imposing them on all density matrices, or on all pure states. No sign condition is put on $\pi_a, \pi_b$ in clause 1: complete positivity of the output channels forces $\pi_a, \pi_b \ge 0$, so `Real.sqrt` returns the paper's $a$ and $b$. For $N \ge 2$ the fractions are determined by the channel.
--
--   Differences from the source:
--   - encoding: an $N$-dimensional quantum state, $N$ unrestricted → hypothesis $2 \le N$; reason: at $N = 1$ the depolarizing fraction is not determined by the channel (every fraction gives the identity map), so the identity channel would be an isotropic cloner with $\pi_a = \pi_b = 0$; the paper never considers $N = 1$, where there is nothing to clone.
--   - reading: "the domain … inside a particular ellipse … is forbidden" for "all isotropic cloning machines", "cloners whose outputs emerge from (distinct) depolarizing channels" (abstract, p. 2) → clause 1 for every quantum channel $X \to A\otimes B$ whose two outputs are depolarizing; reason: this is the paper's own definition of an isotropic cloner and its claim on p. 2; the derivation in §III C runs inside the Heisenberg cloning machines, but the claim is stated for all isotropic cloners, and the narrower class would make the inequality a restatement of the ellipse (3.20).
--   - reading: "It is a tight inequality … which is saturated with the HCMs" → clause 2: every point of the ellipse with $\pi_a, \pi_b \ge 0$ is attained by some isotropic cloner; reason: tightness and saturation are existence claims; the paper's witness for the point $(a, b)$, $a, b \ge 0$, is the HCM (3.8) with $\hat a = b$, which the statement does not name.
--   - generalization: $\pi_a = a^2$, $\pi_b = b^2$ with $a, b$ real and positive → $\sqrt{\pi_a}\sqrt{\pi_b}$ via `Real.sqrt`, and the hypotheses $\pi_a, \pi_b \ge 0$ in clause 2; reason: the same numbers for $a, b > 0$; clause 2 also covers the two endpoints $(\pi_a, \pi_b) = (1, 0)$ and $(0, 1)$ of the ellipse, so it contains the paper's claim; in clause 1 nonnegativity follows from complete positivity.
--   - encoding: outputs depolarizing on input states → on every matrix $\rho$; reason: a channel is linear and density matrices span all matrices, so the conditions are equivalent.
-- source:
--   Cerf, Asymmetric quantum cloning machines in any dimension, arXiv:quant-ph/9805024v2, abstract p. 1, p. 2, Eq. (1.1), and p. 15, Eq. (3.21)

import Mathlib
import Definitions.Def_CerfCloning_Isotropic_Model

open scoped Matrix ComplexOrder BigOperators
open QAlgorithms

namespace CerfCloning.Isotropic

theorem no_cloning_inequality (N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    (∀ (T : Superop (Fin N) (Fin N × Fin N)) (pa pb : ℝ), IsIsotropicCloner N T pa pb →
        1 ≤ pa + 2 / (N : ℝ) * (Real.sqrt pa * Real.sqrt pb) + pb) ∧
    (∀ pa pb : ℝ, 0 ≤ pa → 0 ≤ pb → pa + 2 / (N : ℝ) * (Real.sqrt pa * Real.sqrt pb) + pb = 1 →
        ∃ T : Superop (Fin N) (Fin N × Fin N), IsIsotropicCloner N T pa pb) := by sorry
end CerfCloning.Isotropic
