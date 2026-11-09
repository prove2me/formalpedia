-- Prove2me | Theorems.Thm_BSCvsBEC_lemma_2_3
-- name    : BSCvsBEC.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:39:38.360492+00:00
-- url     : https://prove2.me/theorems/1d4811e6-a6a3-40a6-b463-4fdb18929305
-- title:
--   Lemma 2.3: tensorization with quantum side information, $0<\alpha\le\infty$
-- statement:
--   Let $\Omega$ be a finite alphabet and $(\omega_a)_{a\in\Omega}$ unit vectors in $\mathbb C^d$, giving product states $|\omega_x\rangle$ for $x\in\Omega^n$. Fix $0<\alpha\le\infty$ and $0\le\lambda\le1$, and let $H_\alpha$ be the Rényi entropy of a state. For side information $(P_x)_x$ on a register $Z$ (positive semidefinite, total trace $1$) consider $\sigma_{XYZ}=\sum_x|x\rangle\langle x|\otimes|\omega_x\rangle\langle\omega_x|\otimes P_x$.
--
--   Suppose that for $n=1$, every side information register $Z$, and all $(P_x)_{x\in\Omega}$,
--   $$H_\alpha(YZ)_\sigma\ \ge\ \lambda H_\alpha(XZ)_\sigma+(1-\lambda)H_\alpha(Z)_\sigma. \tag{28}$$
--   Then:
--   1. for every $n$, every side information register $Z$ and all $(P_x)_{x\in\Omega^n}$,
--   $$H_\alpha(YZ)_\sigma\ \ge\ \mathbb E_{R\sim\lambda}\,H_\alpha(X_RZ)_\sigma; \tag{29}$$
--   2. for a random $X\in\Omega^n$ sent through the channel ($Z$ one-dimensional),
--   $$H_\alpha(Y)\ \ge\ \mathbb E_{R\sim\lambda}\,H_\alpha(X_R). \tag{30}$$
--
--   With $\alpha=1$ and $\lambda=\sin^2\theta$ the hypothesis is Theorem 4.2 and conclusion 2 is Theorem 4.1.
--
--   Differences from the source:
--   - generalization: qPSC_θ: |Ω| = q, ℂ^q, ⟨ω_x|ω_x′⟩ = cos θ, with 0 ≤ θ ≤ π/2 fixed → any finite Ω, any d, any family of unit vectors ω : Ω → ℂ^d; θ omitted; reason: p.7: the argument 'holds exactly the same for any tensor power of cq channel'; a qPSC_θ family is one such ω, and θ enters only through ω
--   - encoding: every side information register Z → every finite type ζ (register ℂ^ζ) and every PSD family with total trace 1 (IsSideInfo); reason: finite-dimensional registers are ℂ^ζ up to isomorphism
--   - encoding: 0 < α ≤ ∞ → α : ℝ≥0∞ with α ≠ 0, H_α = renyi α; reason: Lean convention; same instances
--   - encoding: n = 1, labels x ∈ Ω → labels x : Fin 1 → Ω; reason: Lean convention; Ω¹ ≅ Ω
--   - encoding: classical H_α(X_R) → renyi α of the diagonal matrix of the pmf of X_R; reason: the paper's H_α of a register is H_α of its spectrum
--   - encoding: a random variable X on a finite set → its pmf P with IsPMF P; reason: Lean convention; same instances
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Lemma 2.3, eqs. (28)–(30), pp.7–8; state (27), p.7

import Mathlib
import Definitions.Def_BSCvsBEC_shannon
import Definitions.Def_BSCvsBEC_expectSubset
import Definitions.Def_BSCvsBEC_condEntPSC
import Definitions.Def_BSCvsBEC_renyi
import Definitions.Def_BSCvsBEC_stYZ

namespace BSCvsBEC

/-- **Lemma 2.3 (pp.7–8, tensorization).** Fix `0 < α ≤ ∞` and `0 ≤ λ ≤ 1`. Suppose that for `n = 1`,
every side information register `Z` and all `(P_x)_{x∈Ω}`, the state `σ = σ^{(1)}` satisfies
`H_α(YZ)_σ ≥ λ H_α(XZ)_σ + (1 − λ) H_α(Z)_σ` (eq. (28)). Then for every `n`, every `Z` and all
`(P_x)_{x∈Ωⁿ}`, `H_α(YZ)_σ ≥ E_{R∼λ} H_α(X_R Z)_σ` (eq. (29)); and for a random `X ∈ Ωⁿ` sent through
the channel, `H_α(Y) ≥ E_{R∼λ} H_α(X_R)` (eq. (30)).
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Lemma 2.3, pp.7–8, with the states of eq. (27), p.7.

**Formalization Note.** Stated for any finite alphabet `Ω`, any dimension `d` and any family of unit
vectors `ω : Ω → ℂ^d` (the page states it for `qPSC_θ`, and notes on p.7 that the argument "holds
exactly the same for any tensor power of cq channel"); `θ` then plays no role. "Every side
information register `Z`" is every finite type `ζ` (register `ℂ^ζ`) with every `IsSideInfo` family.
In the hypothesis (`n = 1`) labels are `Fin 1 → Ω`. `H_α` is `renyi α` (`α : ℝ≥0∞`, `α = ⊤` the
min-entropy, `α = 1` von Neumann). In (30), `H_α(X_R)` is `renyi α` of the diagonal matrix of the
marginal pmf of `X_R`. -/
theorem lemma_2_3 {Ω : Type} [Fintype Ω] [DecidableEq Ω] {d : ℕ}
    (ω : Ω → EuclideanSpace ℂ (Fin d)) (hω : ∀ a, ‖ω a‖ = 1)
    (α : ENNReal) (hα : α ≠ 0) (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (h28 : ∀ (ζ : Type) [Fintype ζ] [DecidableEq ζ] (P : (Fin 1 → Ω) → Matrix ζ ζ ℂ),
      IsSideInfo P →
        lam * renyi α (stXZ P) + (1 - lam) * renyi α (stZ P) ≤ renyi α (stYZ (pscVec ω) P)) :
    (∀ (n : ℕ) (ζ : Type) [Fintype ζ] [DecidableEq ζ] (P : (Fin n → Ω) → Matrix ζ ζ ℂ),
      IsSideInfo P →
        expectSubset lam n (fun R => renyi α (stXRZ R P)) ≤ renyi α (stYZ (pscVec ω) P)) ∧
    (∀ (n : ℕ) (P : (Fin n → Ω) → ℝ), IsPMF P →
        expectSubset lam n
            (fun R => renyi α (Matrix.diagonal (fun u => ((margR R P u : ℝ) : ℂ)))) ≤
          renyi α (outState P (pscVec ω))) := by sorry

end BSCvsBEC
