-- Prove2me | Theorems.Thm_BlockBochner_Supplement_theorem_5
-- name    : BlockBochner.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:33:30.605189+00:00
-- url     : https://prove2.me/theorems/51499d44-a391-49d7-9c9d-fa11c8157a5b
-- title:
--   Theorem 5 — $O(N)$ model: Glauber spectral gap $\ge(1-\|J_{\mathrm{abs}}\|_{\mathrm{op}}/N)/n$ and $O_{N,\varepsilon_0}(n^2)$ mixing
-- statement:
--   Let $N\ge2$, let $V$ be a finite nonempty set of $n=|V|$ sites, let $J=(J_{xy})$ be a real symmetric $V\times V$ matrix with zero diagonal, let $h=(h_x)_{x\in V}$ be arbitrary external fields in $\mathbb R^N$, and let $\mu=\mu_{J,h}$ be the $O(N)$ Gibbs measure (1) on $(S^{N-1})^V$. Write $J_{\mathrm{abs}}=(|J_{xy}|)$ and $L_{\mathrm{Glaub}}$ for the Glauber Laplacian of $\mu$ on $L^2(\mu)$.
--
--   1. **Spectral gap.** For every such $N,V,J,h$,
--   $$
--   \lambda_2(L_{\mathrm{Glaub}})\ \ge\ \frac{1-\|J_{\mathrm{abs}}\|_{\mathrm{op}}/N}{n}.
--   $$
--   2. **Mixing.** For every $N\ge2$ and every $\varepsilon_0\in(0,1)$ there is a constant $C=C(N,\varepsilon_0)>0$ such that for every finite nonempty $V$, every symmetric zero-diagonal $J$ with $\|J_{\mathrm{abs}}\|_{\mathrm{op}}\le(1-\varepsilon_0)N$ and all external fields $h$, the mixing time of Glauber dynamics satisfies
--   $$
--   t_{\mathrm{mix}}\ \le\ C\,n^2 .
--   $$
--
--   The spectral gap holds throughout $\|J_{\mathrm{abs}}\|_{\mathrm{op}}<N$, in particular whenever every row sum $\sum_{y\ne x}|J_{xy}|$ is below $N$; the constant $N$ is sharp for a uniform gap of order $1/n$.
--
--   **Formalization Note** $\lambda_2(L)\ge\gamma$ is the base mission's `GapAtLeast L γ` ($\gamma\langle f,Lf\rangle\le\|Lf\|^2$ for all $f$, and $\dim\ker L\le1$). The graph of the paper only restricts the support of $J$, so $J$ ranges over all symmetric zero-diagonal matrices. The mixing time is the worst-case-start total-variation mixing time (threshold $1/4$) of the explicit Glauber kernel; $t_{\mathrm{mix}}\le Cn^2$ is written as $t_{\mathrm{mix}}\le\lfloor Cn^2\rfloor$, which is equivalent because mixing times are integers. $C$ is chosen before $V$, $J$ and $h$.
--
--   Differences from the source:
--   - encoding: a finite nonempty graph G with J symmetric, J_xx = 0 and J_xy = 0 unless x ∼ y → an arbitrary symmetric zero-diagonal J on a finite nonempty site type V; reason: the graph only restricts the support of J; every such J is supported on the complete graph, so the family of measures is the same
--   - generalization: λ₂(L_Glaub) ≥ (1 − ‖J_abs‖_op/N)/n, vacuous when the right side is ≤ 0 → GapAtLeast, which also asserts dim ker L_Glaub ≤ 1 for every J; reason: a stronger conclusion; it holds because µ_{J,h} has a strictly positive density with respect to ω^⊗V and so is connected (p.27); it specializes to the source's bound
--   - encoding: spectral gap λ₂(L) as the maximal λ ≥ 0 with L² − λL ⪰ 0 → GapAtLeast L γ: γ⟨f, Lf⟩ ≤ ‖Lf‖² for all f and dim ker L ≤ 1; reason: equivalent to λ₂(L) ≥ γ for γ > 0 and self-adjoint L (base mission convention)
--   - encoding: mixes in O_{N,ε₀}(n²), uniformly in the external fields → ∃ C > 0 depending only on N and ε₀, chosen before V, J, h, with mixingTime ≤ ⌊C n²⌋; reason: mixing times are integers; the O(·) constant may depend only on N and ε₀
--   - encoding: Glauber dynamics resampling from the µ-conditional distribution → the explicit kernel resampling σ_x from the tilted Haar measure ν_{h_x + Σ_{y≠x} J_xy σ_y}; reason: this is the conditional law of σ_x given the other spins under µ_{J,h} (p.27); an explicit version is needed because the mixing time takes a supremum over every starting configuration
--   - encoding: ω the uniform probability measure on S^{N−1} → Mathlib's surface measure volume.toSphere normalized to mass 1; reason: the same rotation-invariant probability measure
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228 (sha256 e4bc2683…4a27706), Theorem 5, p.5 (PDF p.6); restated Sec. 4, pp.26–27 (PDF pp.27–28); setting Sec. 1.3, Eq. (1), p.4 (PDF p.5); mixing time Sec. 1.1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_BlockBochner_GapAtLeast
import Definitions.Def_BlockBochner_glauberLap
import Definitions.Def_BlockBochner_Supplement_onGibbs
import Definitions.Def_BlockBochner_Supplement_absOpNorm
import Definitions.Def_BlockBochner_Supplement_glauberKernel
import Definitions.Def_BlockBochner_Supplement_mixingTime

open MeasureTheory ProbabilityTheory

universe u

namespace BlockBochner.Supplement

/-- **Theorem 5 (O(N) model).** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Theorem 5, p.26–27 (Sec. 4; also
stated on p.5): "Let `N ≥ 2`, and let `µ` be the O(N) Gibbs measure (1) on a finite nonempty graph
with arbitrary external fields. Then the spectral gap of Glauber dynamics is at least
`(1 − ‖J_abs‖_op/N)/n`. Consequently, for every `ε₀ ∈ (0, 1)`, if `‖J_abs‖_op ≤ (1 − ε₀)N`, then
Glauber dynamics mixes in `O_{N,ε₀}(n²)`, uniformly in the external fields."

1. For every `N ≥ 2`, every finite nonempty site set `V` (`n = |V|`), every symmetric
   zero-diagonal `J` and all fields `h`: `λ₂(L_Glaub) ≥ (1 − ‖J_abs‖_op/N)/n` for `µ_{J,h}`.
2. For every `N ≥ 2` and `ε₀ ∈ (0, 1)` there is a constant `C > 0` (depending only on `N, ε₀`)
   such that for every `V`, `J` with `‖J_abs‖_op ≤ (1 − ε₀)N` and `h`: `t_mix ≤ C n²`.

**Formalization Note** The graph only restricts the support of `J` (`J_xy = 0` unless `x ∼ y`),
so it is dropped and `J` ranges over all symmetric zero-diagonal matrices (any such `J` is supported
on the complete graph). `λ₂(L) ≥ γ` is the published `GapAtLeast L γ` (which also asserts
`dim ker L ≤ 1` when `γ ≤ 0`). `t_mix ≤ C n²` is `mixingTime ≤ ⌊C n²⌋`, equivalent since mixing
times are integers. The mixing time uses the pointwise Glauber kernel `glauberKernel`. -/
theorem theorem_5 :
    (∀ N : ℕ, 2 ≤ N → ∀ (V : Type u) [Fintype V] [DecidableEq V] [Nonempty V]
      (J : Matrix V V ℝ), J.IsSymm → (∀ x, J x x = 0) → ∀ h : V → EuclideanSpace ℝ (Fin N),
      GapAtLeast (glauberLap (X := fun _ : V => GraphNNSphere.Sph N) (onGibbs N J h))
        ((1 - absOpNorm J / N) / Fintype.card V)) ∧
    (∀ N : ℕ, 2 ≤ N → ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] [Nonempty V] (J : Matrix V V ℝ), J.IsSymm →
        (∀ x, J x x = 0) → absOpNorm J ≤ (1 - ε₀) * N → ∀ h : V → EuclideanSpace ℝ (Fin N),
        mixingTime (glauberKernel N J h) (onGibbs N J h) ≤
          ((⌊C * (Fintype.card V : ℝ) ^ 2⌋₊ : ℕ) : ℕ∞)) := by sorry

end BlockBochner.Supplement
