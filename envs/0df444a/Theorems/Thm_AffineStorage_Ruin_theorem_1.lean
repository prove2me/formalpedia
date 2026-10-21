-- Prove2me | Theorems.Thm_AffineStorage_Ruin_theorem_1
-- name    : AffineStorage.Ruin.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:39.907327+00:00
-- url     : https://prove2.me/theorems/dede9ca9-5f92-4e2e-9d79-c4148dbcd7e0
-- title:
--   Theorem 1, p. 1288 (PDF 9) — for p > 0, φ(ϑ) is the closed form (9) with ϱ(0), φ(μ) given by (12)
-- statement:
--   Consider the insurance surplus process with premium rate $p>0$, interest rate $r>0$, exponential capital injections (rate $\lambda_+$, mean size $\mu^{-1}$), claims with density $d$ arriving at rate $\lambda_-$, and an independent exponential horizon $T_\nu$. Let
--   $$\varphi(\vartheta)=\int_0^\infty\vartheta e^{-\vartheta x}\,\mathbb E\big(e^{-\alpha\tau_x+\beta X_{\tau_x}-\gamma X_{\tau_x-}}1_{\{\tau_x<T_\nu\}}\,\big|\,X_0=x\big)\,dx$$
--   be the joint transform of the ruin time $\tau_x$, the overshoot $X_{\tau_x}$ and the undershoot $X_{\tau_x-}$, from an exponentially distributed initial surplus. Let $\varrho(0)$ be the same expectation from $X_0=0$.
--
--   Let $F_\star$ be any primitive, on $(0,\mu)\cup(\mu,\infty)$, of the function $F$ of Proposition 1. Let $I_k(\vartheta)=\int_\vartheta^\infty G_k(\eta)e^{-F_\star(\eta)}\,d\eta$ for $k=1,2,3$, and $G=\varrho(0)G_1+\varphi(\mu)G_2+G_3$. Then:
--
--   1. for every $\vartheta>0$, $\vartheta\ne\mu$,
--   $$\varphi(\vartheta)=-\Big(\int_\vartheta^\infty G(\eta)\exp(-F_\star(\eta))\,d\eta\Big)\exp(F_\star(\vartheta));\tag{9}$$
--   2. the determinant $\Delta=I_1(0)I_2(\mu)-I_1(\mu)I_2(0)$ is nonzero;
--   3. the constants are
--   $$\varrho(0)=-\frac{I_3(0)I_2(\mu)-I_3(\mu)I_2(0)}{\Delta},\qquad\varphi(\mu)=-\frac{I_1(0)I_3(\mu)-I_1(\mu)I_3(0)}{\Delta}.\tag{12}$$
--
--   This expresses the transform entirely in terms of the model's data ($p,r,\lambda_\pm,\mu,\nu,\alpha,\beta,\gamma$ and the claim transform $\delta$) through one-dimensional integrals.
--
--   **Formalization Note.** Part 2 is the presupposition of "given by (12)": the page solves the linear system (10)–(11) by Cramer's rule without stating that its determinant is nonzero. The added hypotheses $r>0$, $\lambda_\pm>0$, $\mu>0$ are those of the model definition. The point $\vartheta=\mu$, where $F_\star$ is singular, is excluded from part 1; $\varphi(\mu)$ is given by part 3. The statement holds for every choice of the two additive constants in $F_\star$.
-- source:
--   Boxma & Mandjes, Affine storage and insurance risk models, Math. Oper. Res. 46(4) (2021), p. 1288 (PDF 9), Theorem 1 with eq. (12); eq. (9) p. 1287 (PDF 8)

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace AffineStorage.Ruin

theorem theorem_1 (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (Fs : ℝ → ℝ) (hF : IsPrimitiveF P Fs) :
    let ρ0 := rho B P 0
    let φμ := phi B P P.μ
    let Δ := I (G1 P) Fs 0 * I (G2 P) Fs P.μ - I (G1 P) Fs P.μ * I (G2 P) Fs 0
    (∀ ϑ, 0 < ϑ → ϑ ≠ P.μ →
        phi B P ϑ = -(∫ η in Set.Ioi ϑ, G P ρ0 φμ η * Real.exp (-(Fs η)))
          * Real.exp (Fs ϑ)) ∧
    Δ ≠ 0 ∧
    ρ0 = -(I (G3 P) Fs 0 * I (G2 P) Fs P.μ - I (G3 P) Fs P.μ * I (G2 P) Fs 0) / Δ ∧
    φμ = -(I (G1 P) Fs 0 * I (G3 P) Fs P.μ - I (G1 P) Fs P.μ * I (G3 P) Fs 0) / Δ := by sorry

end AffineStorage.Ruin
