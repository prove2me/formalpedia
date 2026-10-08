-- Prove2me | Theorems.Thm_DisplMonoMFG_WellPosed_proposition_6_2_iii
-- name    : DisplMonoMFG.WellPosed.proposition_6_2_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:25:34.28755+00:00
-- url     : https://prove2.me/theorems/561a5ddb-f515-4c52-927d-7db6e591670f
-- title:
--   Proposition 6.2(iii) with (6.7) — local classical well-posedness of the master equation, $\delta$ independent of $L_1^G$
-- statement:
--   Let $T>0$, $C_0>0$, $L_0^G$ and a function $L^H$ be given. There are $\delta=\delta(L_2^G)>0$ and $C_1^\mu=C_1^\mu(L_1^G)>0$ with the following property.
--
--   Let $\beta\ge0$, and suppose that
--   - $G$ satisfies Assumption 3.1(i) with constants $L_0^G,L_1^G$, Assumption 3.1(ii), and the $W_2$-Lipschitz bound of Remark 3.3(ii) with constant $L_2^G$;
--   - $H$ satisfies Assumption 3.2(i) with $L^H$, 3.2(ii), and 3.2(iii) with $C_0$, and $H(x,\mu,\cdot)$ is convex for every $(x,\mu)$ (the paper's standing assumption, p. 2179).
--
--   Then for every $t_0\in[0,T]$ with $T-t_0\le\delta$:
--   1. The master equation (1.1) has a classical solution $V$ on $[t_0,T]$, and $V(t,\cdot,\cdot),\partial_xV(t,\cdot,\cdot),\partial_{xx}V(t,\cdot,\cdot)\in\mathcal C^2(\mathbb R^d\times\mathcal P_2)$ and $\partial_\mu V(t,\cdot,\cdot,\cdot),\partial_{x\mu}V(t,\cdot,\cdot,\cdot)\in\mathcal C^2(\mathbb R^d\times\mathcal P_2\times\mathbb R^d)$, with all their derivatives continuous in time and uniformly bounded.
--   2. The derivative bound (6.7) holds:
--   $$
--   |\partial_\mu V(t_0,x,\mu,\tilde x)|\le C_1^\mu,\qquad|\partial_{x\mu}V(t_0,x,\mu,\tilde x)|\le C_1^\mu.
--   $$
--   3. $V$ is unique: every classical solution on $[t_0,T]$ with bounded $\partial_xV,\partial_{xx}V,\partial_\mu V,\partial_{x\mu}V$ coincides with $V$ on $[t_0,T]\times\mathbb R^d\times\mathcal P_2$.
--
--   The short-time horizon $\delta$ depends on $L_2^G$ but not on $L_1^G$, while $C_1^\mu$ depends on $L_1^G$; the paper calls this observation crucial. The proof of Theorem 6.3 applies the proposition repeatedly on intervals of length $\delta/2$, with the terminal data controlled by Theorems 4.1 and 5.1.
--
--   **Formalization Note** On the page, $\delta$ depends only on $d,L_0^G,L_2^G,L^H(C_1^x)$, and $C_1^\mu$ only on $d,L_0^G,L_1^G,L^H(C_1^x)$, where $C_1^x$ is the constant of (6.2). Proposition 6.1 defines $C_1^x$ through a BSDE and shows that it depends only on $d,T,C_0,L_0^G,L^H$. This expanded dependence is used: $\delta$ and $C_1^\mu$ are functions of $L_2^G$ and $L_1^G$ respectively, chosen after $d,T,C_0,L_0^G,L^H$ and before everything else. Uniqueness is stated within the bounded-derivative class, the class in which the proof of Theorem 6.3 invokes it. Parts (i) and (ii) (the representation (6.6)) and the identity (2.27) concern McKean–Vlasov FBSDEs and are not formalized. Assumption 3.5 is not assumed. Assumption 3.2(iv) is not assumed either, so the convexity of $H(x,\mu,\cdot)$, which the paper always assumes (p. 2179), is a separate hypothesis.
-- source:
--   Gangbo, Mészáros, Mou, Zhang, Mean field games master equations with nonseparable Hamiltonians and displacement monotonicity, Ann. Probab. 50 (2022), Proposition 6.2(iii) and (6.7), pp. 2206–2207

import Mathlib
import Definitions.Def_DisplMonoMFG_WellPosed_Master

open MeasureTheory

namespace DisplMonoMFG.WellPosed

/-- Gangbo, Mészáros, Mou, Zhang, Ann. Probab. 50 (2022), Proposition 6.2(iii) with (6.7),
pp. 2206–2207 (PDF pp. 29–30): under Assumptions 3.1 and 3.2(i)–(iii) there is `δ > 0` such that
whenever `T - t₀ ≤ δ` the master equation (1.1) has a unique classical solution `V` on `[t₀, T]`,
with the further regularity of Theorem 4.1, and `|∂_μ V(t₀, x, μ, x̃)|, |∂_xμ V(t₀, x, μ, x̃)| ≤ C₁^μ`.
`δ` depends only on `d, T, C₀, L₀^G, L^H` and `L₂^G` — not on `L₁^G` — and `C₁^μ` only on
`d, T, C₀, L₀^G, L^H` and `L₁^G` (as functions `δ(L₂)` and `C₁(L₁)`).
Formalization Notes: the page says `δ` depends on `d, L₀^G, L₂^G, L^H(C₁^x)` and `C₁^μ` on
`d, L₀^G, L₁^G, L^H(C₁^x)`, where the constant `C₁^x` of (6.2) depends only on `d, T, C₀, L₀^G` and
`L^H`; this expanded dependence is used. Uniqueness is stated in the class of classical solutions
with bounded `∂_x V, ∂_xx V, ∂_μ V, ∂_xμ V`, the class in which Theorem 6.3's proof uses it.
Parts (i), (ii) and the identity (2.27) concern McKean–Vlasov FBSDEs and are not formalized.
`H(x, μ, ·)` is convex: the paper's standing assumption (p. 2179, "We always assume `H(x, μ, ·)`
to be convex"); Proposition 6.2 does not assume 3.2(iv), so it is stated separately. -/
theorem proposition_6_2_iii :
    ∀ (d : ℕ) (T C₀ L₀ : ℝ) (LH : ℝ → ℝ), 0 < T →
      ∃ δ C₁ : ℝ → ℝ, (∀ L₂, 0 < δ L₂) ∧ (∀ L₁, 0 < C₁ L₁) ∧
      ∀ (L₁ L₂ β : ℝ), 0 ≤ β → ∀ (H : E d → P2 d → E d → ℝ) (G : E d → P2 d → ℝ)
        (wH : C2W d (E d × E d) ℝ) (wG : C2W d (E d) ℝ),
        Assm31i G wG L₀ L₁ → Assm31ii G wG → LipW2 G wG L₂ →
        Assm32i H wH LH → Assm32ii H wH → Assm32iii wH C₀ →
        (∀ (x : E d) (μ : P2 d), ConvexOn ℝ Set.univ (H x μ)) →
        ∀ t₀ ∈ Set.Icc (0 : ℝ) T, T - t₀ ≤ δ L₂ →
          ∃ (V Vt : ℝ → E d → P2 d → ℝ) (w : ℝ → C2W d (E d) ℝ),
            IsClassicalSol β t₀ T H G V Vt w ∧ HighReg (Set.Icc t₀ T) V w ∧
            (∀ (x : E d) (μ : P2 d) (y : E d),
              ‖(w t₀).Dm x μ y‖ ≤ C₁ L₁ ∧ ‖(w t₀).DxDm x μ y‖ ≤ C₁ L₁) ∧
            ∀ V' : ℝ → E d → P2 d → ℝ, IsClassicalSolBdd β t₀ T H G V' →
              ∀ t ∈ Set.Icc t₀ T, ∀ (x : E d) (μ : P2 d), V' t x μ = V t x μ := by sorry

end DisplMonoMFG.WellPosed
