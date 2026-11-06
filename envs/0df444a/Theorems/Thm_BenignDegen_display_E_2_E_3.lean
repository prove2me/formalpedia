-- Prove2me | Theorems.Thm_BenignDegen_display_E_2_E_3
-- name    : BenignDegen.display_E_2_E_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:05.128701+00:00
-- url     : https://prove2.me/theorems/85082fca-9b72-448e-a074-a488c0a799f7
-- title:
--   (E.2)–(E.3) — $\Pi_+'(X_\star-\sigma S;\cdot)=\mathscr J_S$ and $\delta_\sigma'=-\Psi_S$ on $\mathrm{ri}\,\mathcal S_\star$; the boundary correction term
-- statement:
--   Let $1\le d\le n$, let $f$ be a square-free polynomial with $\deg f\le 2d$, and suppose the order-$d$ relaxation is uniquely rank-one exact, $\operatorname{argmin}(\mathrm P_d)=\{X_\star\}$ with $X_\star=b_d(x_\star)b_d(x_\star)^\top=Nqq^\top$, and admits a strictly complementary certificate. Let $(\mathcal A,b)$ be a surjective equality encoding with $\{X:\mathcal AX=b\}=I_N+\mathcal T_d$ and cost $C=C_f$ (e.g. (B.3)); $\mathsf P,\mathsf P^\perp$, $\delta_\sigma$, $\mathcal Z_\star$ are those of this SDP, $V=q^\perp$, and $\mathcal S_\star$ is the set (2.4). Fix $\sigma>0$ and $S\in\mathcal S_\star$, let $K=\ker S\cap V$ and $Q_K$ an orthonormal basis of $K$. Then
--
--   $$
--   S\in\operatorname{ri}\mathcal S_\star:\quad \Pi_+'(X_\star-\sigma S;\cdot)=\mathscr J_S,\qquad \delta_\sigma'(X_\star-\sigma S;\cdot)=-\Psi_S, \tag{E.2}
--   $$
--
--   $$
--   S\in\mathcal S_\star\ \text{arbitrary}:\quad \Pi_+'(X_\star-\sigma S;H)=\mathscr J_S(H)+Q_K\Pi_+(Q_K^\top HQ_K)Q_K^\top. \tag{E.3}
--   $$
--
--   So $\Psi_S$ is a continuous algebraic extension of the interior derivative, and at a boundary certificate the true derivative acquires exactly one extra nonlinear term.
--
--   Differences from the source:
--   - generalization: the independent encoding (B.3) of (P_d) (A = A_d, b = e₁) → any surjective A : S^N → ℝ^κ with {X : AX = b} = I_N + T_d, and C = C_f; reason: δ_σ, Z⋆, the cones and the optimal sets depend on A only through P (the projector onto R_d) and X_b (= I_N), and the algorithmic results hold for every surjective A; (B.3) is an instance by Proposition B.1
--   - encoding: square-free f, I_d, {±1}ⁿ, '≡ (mod I_B)' → coefficient function Finset (Fin n) → ℝ, {T : Finset (Fin n) // T.card ≤ d}, Fin n → ℤˣ, equality of square-free coefficients through G_d (B.2); reason: the same objects; I_d = {T : |T| ≤ min{d, n}} because |T| ≤ n always
--   - encoding: S^p, ℝ^m → SymMat ι over a finite index type (Frobenius inner product), EuclideanSpace ℝ κ; reason: the same spaces with p = |ι|, m = |κ|; every quantifier ranges over symmetric matrices as in the source
--   - encoding: Π₊ the Frobenius projection onto S^p_+, Π₋ = Id − Π₊ → published metricProj onto psdCone (a chosen nearest point), PiMinus = Id − PiPlus; reason: S^p_+ is closed and convex, so the nearest point exists and is unique; the same map
--   - encoding: A† := A^*(AA^*)^{-1}, P = A†A → Apinv via ContinuousLinearMap.inverse of A ∘ A^*; P the orthogonal projector onto ran A^*; reason: A is surjective (the standing assumption of (3.1), carried as a hypothesis), so AA^* is invertible and A†A is the orthogonal projector onto ran A^*
--   - encoding: directional derivative F′(z; h) := lim_{t↓0}(F(z+th) − F(z))/t → published NonsmoothNewton.Local.HasDirDerivAt (one-sided limit over t > 0); reason: the same limit
--   - encoding: Q_K from the eigen-chart (C.3) → any orthonormal basis Q_K of K = ker S ∩ V; reason: the term Q_K Π₊(Q_K^⊤HQ_K) Q_K^⊤ does not depend on the choice of orthonormal basis
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, Appendix E.2, (E.2)–(E.3), p.25; (4.4), p.9

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Displays (E.2)–(E.3), Appendix E.2, Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.25.
In the setting of Theorem 4.3, fix `σ > 0` and `S ∈ S_⋆`, `X_⋆ = b_d(x_⋆)b_d(x_⋆)^⊤`.
(E.2) If `S ∈ ri S_⋆`: `Π'₊(X_⋆ − σS; ·) = J_S` and `δ'_σ(X_⋆ − σS; ·) = −Ψ_S`.
(E.3) For every `S ∈ S_⋆`, with `Q_K` an orthonormal basis of `K = ker(S) ∩ V`:
`Π'₊(X_⋆ − σS; H) = J_S(H) + Q_K Π₊(Q_K^⊤ H Q_K) Q_K^⊤`.

**Formalization Note** Directional derivatives are one-sided (`HasDirDerivAt`). `S_⋆` is the
set (2.4) with `f_⋆ = OPT(f)`; the encoding `D` is any surjective `A` with
`{X : AX = b} = I_N + T_d` and `C = C_f`. `Q_K` is any orthonormal basis of `K`. -/
theorem display_E_2_E_3 (n d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n) (f : Finset (Fin n) → ℝ)
    (hdeg : DegLe f (2 * d)) (x : Fin n → ℤˣ) (hopt : UniqueRankOneOpt n d f x)
    (hsc : HasSCCertificate n d f) {κ : Type} [Fintype κ] [DecidableEq κ]
    (D : SDPData (Idx n d) κ) (hA : Function.Surjective D.A) (henc : IsBoolEncoding D)
    (hC : D.C = Cf n d f) (σ : ℝ) (hσ : 0 < σ) :
    (∀ S ∈ intrinsicInterior ℝ (gramCerts n d f (cubeMin f)), ∀ H : SymMat (Idx n d),
      NonsmoothNewton.Local.HasDirDerivAt PiPlus (rankOne (bvec n d x) - σ • S) H
        (Jmap n d x σ S H) ∧
      NonsmoothNewton.Local.HasDirDerivAt (D.delta σ) (rankOne (bvec n d x) - σ • S) H
        (-Psi D x σ S H)) ∧
    (∀ S ∈ gramCerts n d f (cubeMin f), ∀ (k : ℕ)
      (QK : OrthonormalBasis (Fin k) ℝ ↥(kerSub S ⊓ Vq n d x)), ∀ H : SymMat (Idx n d),
      NonsmoothNewton.Local.HasDirDerivAt PiPlus (rankOne (bvec n d x) - σ • S) H
        (Jmap n d x σ S H +
          compressPlus (fun j => (QK j : EuclideanSpace ℝ (Idx n d))) H)) := by sorry

end BenignDegen
