-- Prove2me | Theorems.Thm_BenignDegen_theorem_4_3
-- name    : BenignDegen.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:54.797016+00:00
-- url     : https://prove2.me/theorems/b6823b59-605a-41cc-bdd9-1c0d961fc70f
-- title:
--   Theorem 4.3 — deterministic Boolean benign degeneracy: error bound, stall cone = tangent cone, and linear ADMM, sGS–ADMM, PDHG
-- statement:
--   Let $1\le d\le n$ and let $f$ be a square-free polynomial on $\{\pm1\}^n$ with $\deg f\le2d$. Suppose the order-$d$ Boolean moment relaxation $(\mathrm P_d)$ has a **unique rank-one optimum**, $\operatorname{argmin}(\mathrm P_d)=\{b_d(x_\star)b_d(x_\star)^\top\}$ for a cube point $x_\star$, and **one strictly complementary optimal SOS certificate**, i.e. some $S\in\mathcal S_\star$ (2.4) with $\operatorname{rank}S=N-1$. Let $(\mathcal A,b)$ be a surjective equality encoding of $(\mathrm P_d)$ with $\{X:\mathcal AX=b\}=I_N+\mathcal T_d$ (for instance the independent encoding (B.3)) and cost $C=C_f$. Then:
--
--   1. for every fixed $\sigma>0$ the canonical DR residual satisfies the setwise error bound (3.9) around its entire fixed-point set $\mathcal Z_\star$;
--   2. for every $\sigma>0$ the stall cone equals the tangent cone at every endpoint: $\mathcal C(\bar Z)=T_{\mathcal Z_\star}(\bar Z)$ for all $\bar Z\in\mathcal Z_\star$;
--   3. for every $\sigma>0$ and $0<\tau<2$, every run of exact ADMM and of exact sGS–ADMM, from every initialization, has the conclusions of Corollary 5.1: the shadow converges to an endpoint, its $\mathsf G_\tau$-distance to $\mathcal Z_\star$ contracts eventually Q-linearly, and the shadow and the raw iterates converge R-linearly (to a KKT triple);
--   4. for all $\eta_x,\eta_y>0$ with $\eta_x\eta_y\|\mathcal A\|_{\rm op}^2<1$, every PDHG run, from every initialization, has the conclusions of Corollary 5.2.
--
--   No condition is placed on the limit point: the conclusions hold at every endpoint, regardless of the rank of the certificate selected by the iteration.
--
--   Differences from the source:
--   - generalization: the independent encoding (B.3) of (P_d) (A = A_d, b = e₁) → any surjective A : S^N → ℝ^κ with {X : AX = b} = I_N + T_d, and C = C_f; reason: δ_σ, Z⋆, the cones and the optimal sets depend on A only through P (the projector onto R_d) and X_b (= I_N), and the algorithmic results hold for every surjective A; (B.3) is an instance by Proposition B.1
--   - encoding: square-free f, I_d, {±1}ⁿ, '≡ (mod I_B)' → coefficient function Finset (Fin n) → ℝ, {T : Finset (Fin n) // T.card ≤ d}, Fin n → ℤˣ, equality of square-free coefficients through G_d (B.2); reason: the same objects; I_d = {T : |T| ≤ min{d, n}} because |T| ≤ n always
--   - encoding: S^p, ℝ^m → SymMat ι over a finite index type (Frobenius inner product), EuclideanSpace ℝ κ; reason: the same spaces with p = |ι|, m = |κ|; every quantifier ranges over symmetric matrices as in the source
--   - encoding: Π₊ the Frobenius projection onto S^p_+, Π₋ = Id − Π₊ → published metricProj onto psdCone (a chosen nearest point), PiMinus = Id − PiPlus; reason: S^p_+ is closed and convex, so the nearest point exists and is unique; the same map
--   - encoding: A† := A^*(AA^*)^{-1}, P = A†A → Apinv via ContinuousLinearMap.inverse of A ∘ A^*; P the orthogonal projector onto ran A^*; reason: A is surjective (the standing assumption of (3.1), carried as a hypothesis), so AA^* is invertible and A†A is the orthogonal projector onto ran A^*
--   - encoding: T_C(z) = {h : ∃ t_k ↓ 0, z_k ∈ C, (z_k − z)/t_k → h} → published SunNLSDP.Equiv.tangentCone (contingent cone via infDist); reason: the two cones coincide for every set
--   - encoding: directional derivative F′(z; h) := lim_{t↓0}(F(z+th) − F(z))/t → published NonsmoothNewton.Local.HasDirDerivAt (one-sided limit over t > 0); reason: the same limit
--   - encoding: R-linear convergence, eventual Q-linear contraction → RLinearTo (‖u_k − ū‖ ≤ cρ^k for all k, 0 ≤ ρ < 1), EventuallyQLinear (d_{k+1} ≤ ρ d_k for all k ≥ K, 0 ≤ ρ < 1); reason: the standard definitions; ρ < 1 is strict
--   - encoding: the iterates of an algorithm from an arbitrary initialization → every sequence satisfying the update equations for all k (the unused λ⁰ is free); reason: the same runs, quantified universally
--   - generalization: the limits are an endpoint Z̄ and R-linear limits of the raw iterates → also states that the limits (X̄, λ̄, S̄) form a KKT triple with Z̄ = X̄ − σS̄; reason: shown in the proof (Appendix F.3, p.29: X̄, S̄ are the factors of Z̄ and λ̄ the unique multiplier of S̄); dropping the clause gives the source's statement
--   - encoding: unique rank-one optimum; strictly complementary optimal SOS certificate → argmin(P_d) = {b_d(x⋆)b_d(x⋆)^⊤} for a cube point x⋆ (2.5); ∃ S ∈ S⋆ (2.4) with f⋆ = OPT(f) and rank S = N − 1; reason: the paper's definitions (2.5) and p.5; the first already implies that x⋆ is the unique Boolean minimizer and that the relaxation is exact
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, §4.3, Theorem 4.3, p.9 (with §2 pp.4–5, Corollaries 5.1–5.2 pp.10–11, Proposition B.1 p.14)

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Theorem 4.3 (deterministic Boolean benign degeneracy), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.9.
Suppose the order-`d` Boolean moment relaxation has a unique rank-one optimum
(`argmin(P_d) = {b_d(x_⋆)b_d(x_⋆)^⊤}`, (2.5)) and one strictly complementary optimal SOS
certificate (`S ∈ S_⋆` of (2.4) with `rank S = N − 1`). Then, for every fixed `σ > 0`, the
canonical DR residual satisfies the setwise error bound (3.9) around its entire fixed-point set
`Z_⋆`, and its stall cone equals the tangent cone of `Z_⋆` at every endpoint. The algorithmic
conclusions of Corollaries 5.1 (exact ADMM and exact sGS–ADMM, every `σ > 0`, `0 < τ < 2`, every
initialization) and 5.2 (PDHG, every `η_x, η_y > 0` with `η_xη_y‖A‖²_op < 1`, every
initialization) hold, at every endpoint, regardless of the rank of the certificate selected by
the iteration.

**Formalization Note** The encoding is any surjective `A : S^N → ℝ^κ` with
`{X : AX = b} = I_N + T_d` and `C = C_f`; the independent encoding (B.3) is one such
(Proposition B.1). Standing assumptions of §2: `1 ≤ d ≤ n`, `deg f ≤ 2d`. -/
theorem theorem_4_3 (n d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n) (f : Finset (Fin n) → ℝ)
    (hdeg : DegLe f (2 * d)) (x : Fin n → ℤˣ) (hopt : UniqueRankOneOpt n d f x)
    (hsc : HasSCCertificate n d f) {κ : Type} [Fintype κ] [DecidableEq κ]
    (D : SDPData (Idx n d) κ) (hA : Function.Surjective D.A) (henc : IsBoolEncoding D)
    (hC : D.C = Cf n d f) :
    (∀ σ : ℝ, 0 < σ → D.ErrorBound σ) ∧
    (∀ σ : ℝ, 0 < σ → ∀ Zbar ∈ D.Zstar σ,
      D.stallCone σ Zbar = SunNLSDP.Equiv.tangentCone (D.Zstar σ) Zbar) ∧
    (∀ σ : ℝ, 0 < σ → ∀ τ : ℝ, 0 < τ → τ < 2 →
      (∀ (X S : ℕ → SymMat (Idx n d)) (lam : ℕ → EuclideanSpace ℝ κ),
        D.IsADMMRun σ τ X S lam → D.ADMMConclusions σ τ X S lam) ∧
      (∀ (X S : ℕ → SymMat (Idx n d)) (lamH lam : ℕ → EuclideanSpace ℝ κ),
        D.IsSGSRun σ τ X S lamH lam → D.ADMMConclusions σ τ X S lam)) ∧
    (∀ ηx ηy : ℝ, 0 < ηx → 0 < ηy → ηx * ηy * ‖D.A‖ ^ 2 < 1 →
      ∀ (X : ℕ → SymMat (Idx n d)) (lam : ℕ → EuclideanSpace ℝ κ),
        D.IsPDHGRun ηx ηy X lam → D.PDHGConclusions ηx ηy X lam) := by sorry

end BenignDegen
