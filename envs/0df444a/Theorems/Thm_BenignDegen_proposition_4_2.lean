-- Prove2me | Theorems.Thm_BenignDegen_proposition_4_2
-- name    : BenignDegen.proposition_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:25.911216+00:00
-- url     : https://prove2.me/theorems/867af050-fed1-4866-a4e3-5522c9694660
-- title:
--   Proposition 4.2 — $\ker\Psi_S=\mathcal L$ for every $S\in\mathcal S_\star$ and $\mu_{\rm ri}\ge\mu_\star>0$ (4.5)
-- statement:
--   Let $1\le d\le n$, let $f$ be a square-free polynomial with $\deg f\le 2d$, and suppose the order-$d$ relaxation is uniquely rank-one exact, $\operatorname{argmin}(\mathrm P_d)=\{X_\star\}$ with $X_\star=b_d(x_\star)b_d(x_\star)^\top=Nqq^\top$, and admits a strictly complementary certificate. Let $(\mathcal A,b)$ be a surjective equality encoding with $\{X:\mathcal AX=b\}=I_N+\mathcal T_d$ and cost $C=C_f$ (e.g. (B.3)); $\mathsf P,\mathsf P^\perp$, $\delta_\sigma$, $\mathcal Z_\star$ are those of this SDP, $V=q^\perp$, and $\mathcal S_\star$ is the set (2.4). Fix $\sigma>0$ and let $\mathcal L=\mathcal R\cap\mathbb S(V)$. For every $S\in\mathcal S_\star$ — including boundary certificates — $\ker(\Psi_S)=\mathcal L$; consequently
--
--   $$
--   \mu_{\rm ri}\ \ge\ \mu_\star:=\min_{S\in\mathcal S_\star}\sigma_{\min}\bigl(\Psi_S|_{\mathcal L^\perp}\bigr)\ >\ 0. \tag{4.5}
--   $$
--
--   This verifies condition (i) of Theorem 3.2 for the Boolean moment SDP, from which Theorem 4.3 follows.
--
--   Differences from the source:
--   - generalization: the independent encoding (B.3) of (P_d) (A = A_d, b = e₁) → any surjective A : S^N → ℝ^κ with {X : AX = b} = I_N + T_d, and C = C_f; reason: δ_σ, Z⋆, the cones and the optimal sets depend on A only through P (the projector onto R_d) and X_b (= I_N), and the algorithmic results hold for every surjective A; (B.3) is an instance by Proposition B.1
--   - encoding: square-free f, I_d, {±1}ⁿ, '≡ (mod I_B)' → coefficient function Finset (Fin n) → ℝ, {T : Finset (Fin n) // T.card ≤ d}, Fin n → ℤˣ, equality of square-free coefficients through G_d (B.2); reason: the same objects; I_d = {T : |T| ≤ min{d, n}} because |T| ≤ n always
--   - encoding: S^p, ℝ^m → SymMat ι over a finite index type (Frobenius inner product), EuclideanSpace ℝ κ; reason: the same spaces with p = |ι|, m = |κ|; every quantifier ranges over symmetric matrices as in the source
--   - encoding: Π₊ the Frobenius projection onto S^p_+, Π₋ = Id − Π₊ → published metricProj onto psdCone (a chosen nearest point), PiMinus = Id − PiPlus; reason: S^p_+ is closed and convex, so the nearest point exists and is unique; the same map
--   - encoding: A† := A^*(AA^*)^{-1}, P = A†A → Apinv via ContinuousLinearMap.inverse of A ∘ A^*; P the orthogonal projector onto ran A^*; reason: A is surjective (the standing assumption of (3.1), carried as a hypothesis), so AA^* is invertible and A†A is the orthogonal projector onto ran A^*
--   - encoding: directional derivative F′(z; h) := lim_{t↓0}(F(z+th) − F(z))/t → published NonsmoothNewton.Local.HasDirDerivAt (one-sided limit over t > 0); reason: the same limit
--   - encoding: ri, rb = cl ∖ ri → intrinsicInterior ℝ, relBdry C := C ∖ ri C; reason: rb is only applied to the closed sets X⋆, S⋆, Z⋆, where cl C ∖ ri C = C ∖ ri C
--   - encoding: μ_ri over unit H ∈ D^⊥; μ⋆ = min_S σ_min(Ψ_S|_{L^⊥}) > 0; μ_ri ≥ μ⋆ → unit H ∈ L^⊥ (here M = {0}, D = L); ∃ μ > 0 bounding all ‖Ψ_S H‖ (unit H ∈ L^⊥, S ∈ S⋆) from below; every such lower bound μ also bounds ‖δ′_σ(Z̄; H)‖ for Z̄ ∈ ri Z⋆ (with existence of the derivative); reason: in the Boolean instantiation X⋆ is a point, so M = {0} and D = L; 'every common lower bound of σ_min(Ψ_S|_{L^⊥}) bounds μ_ri' is μ_ri ≥ inf_S σ_min = μ⋆, and the minimum is attained
-- source:
--   Kang, Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations, arXiv:2610.20270v1, §4.2, (4.4), Proposition 4.2, (4.5), p.9

import Mathlib
import Definitions.Def_BenignDegen_SDP
import Definitions.Def_BenignDegen_Geometry
import Definitions.Def_BenignDegen_Convergence
import Definitions.Def_BenignDegen_Algorithms
import Definitions.Def_BenignDegen_Boolean
open SunNLSDP.Equiv Matrix Filter Topology
open scoped RealInnerProductSpace Pointwise

namespace BenignDegen

/-- Proposition 4.2 (uniform relative-interior modulus), Kang, *Benign Degeneracy for First-Order Methods in Exact Boolean Moment–SOS Relaxations*, arXiv:2610.20270v1, p.9.
In the setting of Theorem 4.3 and for `σ > 0`: for every `S ∈ S_⋆`, `ker(Ψ_S) = L`; consequently
`μ_ri ≥ μ_⋆ := min_{S∈S_⋆} σ_min(Ψ_S|_{L^⊥}) > 0` (4.5).

**Formalization Note** `L = R ∩ S(V)` with `V = q^⊥`, and in this instantiation `M = {0}`, `D = L`,
so `μ_ri` is taken over unit `H ∈ L^⊥`. "`μ_⋆ > 0`" is "some `μ > 0` bounds every
`‖Ψ_S H‖`, `S ∈ S_⋆`, `H ∈ L^⊥` unit, from below"; "`μ_ri ≥ μ_⋆`" is "every such lower bound
`μ` also bounds `‖δ'_σ(Z̄; H)‖` for all `Z̄ ∈ ri Z_⋆` and unit `H ∈ L^⊥`". -/
theorem proposition_4_2 (n d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n) (f : Finset (Fin n) → ℝ)
    (hdeg : DegLe f (2 * d)) (x : Fin n → ℤˣ) (hopt : UniqueRankOneOpt n d f x)
    (hsc : HasSCCertificate n d f) {κ : Type} [Fintype κ] [DecidableEq κ]
    (D : SDPData (Idx n d) κ) (hA : Function.Surjective D.A) (henc : IsBoolEncoding D)
    (hC : D.C = Cf n d f) (σ : ℝ) (hσ : 0 < σ) :
    (∀ S ∈ gramCerts n d f (cubeMin f),
      {H : SymMat (Idx n d) | Psi D x σ S H = 0} =
        ((D.rowSpace ⊓ supported (Vq n d x) : Submodule ℝ (SymMat (Idx n d))) :
          Set (SymMat (Idx n d)))) ∧
    (∃ μ : ℝ, 0 < μ ∧ ∀ S ∈ gramCerts n d f (cubeMin f),
      ∀ H ∈ (D.rowSpace ⊓ supported (Vq n d x))ᗮ, ‖H‖ = 1 → μ ≤ ‖Psi D x σ S H‖) ∧
    (∀ μ : ℝ, (∀ S ∈ gramCerts n d f (cubeMin f),
        ∀ H ∈ (D.rowSpace ⊓ supported (Vq n d x))ᗮ, ‖H‖ = 1 → μ ≤ ‖Psi D x σ S H‖) →
      ∀ Zbar ∈ intrinsicInterior ℝ (D.Zstar σ), ∀ H ∈ (D.rowSpace ⊓ supported (Vq n d x))ᗮ,
        ‖H‖ = 1 → ∃ dd, NonsmoothNewton.Local.HasDirDerivAt (D.delta σ) Zbar H dd ∧
          μ ≤ ‖dd‖) := by sorry

end BenignDegen
