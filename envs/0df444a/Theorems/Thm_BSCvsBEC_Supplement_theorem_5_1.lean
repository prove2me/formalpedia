-- Prove2me | Theorems.Thm_BSCvsBEC_Supplement_theorem_5_1
-- name    : BSCvsBEC.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:42:42.768687+00:00
-- url     : https://prove2.me/theorems/49d1aae4-ffb6-4a89-bfa0-874d184b5b35
-- title:
--   Theorem 5.1 — $q$-ary Rényi PSC–BEC comparison $H_\alpha(YZ)_\sigma\ge\mathbb E_{R\sim\tau_\alpha(q,\theta)}H_\alpha(X_RZ)_\sigma$, $2\le\alpha\le\infty$
-- statement:
--   Let $q\ge2$, $0\le\theta\le\pi/2$, $\rho=\cos\theta$, $p=\frac{q-1}q(1-\rho)$, and $\tau_\alpha(q,\theta)=H_\alpha(\mathrm{qSC}_p)/\log q$. Let $(|\omega_i\rangle)_{i}$ be $q$ unit vectors in $\mathbb C^q$ with pairwise inner products $\cos\theta$, and let
--   $$\sigma_{XYZ}=\sum_{x}|x\rangle\langle x|\otimes|\omega_x\rangle\langle\omega_x|\otimes P_x,\qquad P_x\succeq0,\quad\sum_x\mathrm{Tr}\,P_x=1,$$
--   be an $n$-fold $\mathrm{qPSC}_\theta$ state with arbitrary quantum side information $Z$. Then for $2\le\alpha\le\infty$
--   $$H_\alpha(YZ)_\sigma\ \ge\ \mathbb E_{R\sim\tau_\alpha(q,\theta)}H_\alpha(X_RZ)_\sigma,$$
--   and $\tau_\infty(q,\theta)=-\log_q(1-p)$.
--
--   This extends Theorem 4.6 ($\alpha\ge2$) to $q$-ary alphabets. Entropies are in bits, $\tau$ uses base-$q$ logarithms.
--
--   **Formalization Note** The input alphabet is $\{0,\dots,q-1\}$ for every $q\ge2$; the case $\alpha=\infty$ (the min-entropy) is included in the range $2\le\alpha\le\infty$, and the formula for $\tau_\infty$ is the second conjunct.
--
--   Differences from the source:
--   - generalization: inputs x ∈ F_qⁿ for a prime power q → inputs in Fin q for every q ≥ 2 (published IsQPSC); reason: the statement uses no field operation; for a prime power q, relabel F_q by a bijection with Fin q
--   - reading: the case α = ∞ follows by taking the limit α → ∞ → α : ℝ≥0∞ with 2 ≤ α, so α = ⊤ (min-entropy) is included; reason: the page asserts the α = ∞ case
--   - reading: θ unstated in the theorem → 0 ≤ θ ≤ π/2; reason: qPSC_θ is defined for 0 ≤ θ ≤ π/2 (p.5)
--   - reading: some fixed pure states (|ω_x⟩) in the q-dimensional 𝒴 with ⟨ω_x|ω_x'⟩ = cos θ for x ≠ x' → every such family of unit vectors in ℂ^q (IsQPSCOn θ ω); reason: the page fixes an arbitrary such family; the statement is required for each one
--   - encoding: a side information register Z of any finite dimension, P_x ⪰ 0, ∑ₓ Tr P_x = 1 → Z = ℂ^ζ for every finite type ζ, with IsSideInfo P; reason: Lean convention; same instances
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Theorem 5.1, eq. (114), p.23; τ_α(q, θ), p.23

import Mathlib
import Definitions.Def_BSCvsBEC_expectSubset
import Definitions.Def_BSCvsBEC_condEntPSC
import Definitions.Def_BSCvsBEC_renyi
import Definitions.Def_BSCvsBEC_stYZ
import Definitions.Def_BSCvsBEC_mB
import Definitions.Def_BSCvsBEC_Supplement_lamStarB

namespace BSCvsBEC.Supplement

/-- **Theorem 5.1 (p.23, `q`-ary PSC–BEC Rényi comparison).** Let `2 ≤ α < ∞` and let
`σ_XYZ = ∑_{x∈F_qⁿ} |x⟩⟨x| ⊗ |ω_x⟩⟨ω_x| ⊗ P_x`, `P_x ⪰ 0`, `∑ₓ Tr P_x = 1`, be an `n`-fold `qPSC_θ` state
with arbitrary quantum side information `Z`. Then `H_α(YZ)_σ ≥ E_{R∼τ_α(q,θ)} H_α(X_R Z)_σ` (eq. (114)).
The case `α = ∞` follows by taking the limit `α → ∞`; here `τ_∞(q, θ) = −log_q(1 − p)`.
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Theorem 5.1, eq. (114), p.23, with `τ_α(q, θ) := H_α(qSC_p)/log q`, `p = ((q − 1)/q)(1 − cos θ)`
(p.23).

**Formalization Note.** `α : ℝ≥0∞` with `2 ≤ α`, so `α = ∞` (`⊤`, the min-entropy) is included. The
alphabet is `Fin q` for any `q ≥ 2` with the published `IsQPSC θ ω` (unit vectors in `ℂ^q`, pairwise
inner products `cos θ`); the statement uses no field operation, so this contains the `F_q` case.
`θ ∈ [0, π/2]` (the range of `qPSC_θ`, p.5). `Z = ℂ^ζ` for any finite `ζ` and `IsSideInfo` family;
every `n`. Entropies are in bits while `τ` uses `log_q`. The second conjunct is the `τ_∞` formula. -/
theorem theorem_5_1 (q : ℕ) (hq : 2 ≤ q) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2)
    (ω : Fin q → EuclideanSpace ℂ (Fin q)) (hω : BSCvsBEC.IsQPSC θ ω)
    (α : ENNReal) (hα : 2 ≤ α)
    (n : ℕ) (ζ : Type) [Fintype ζ] [DecidableEq ζ] (P : (Fin n → Fin q) → Matrix ζ ζ ℂ)
    (hP : BSCvsBEC.IsSideInfo P) :
    BSCvsBEC.expectSubset (tauQ α q θ) n (fun R => BSCvsBEC.renyi α (BSCvsBEC.stXRZ R P)) ≤
      BSCvsBEC.renyi α (BSCvsBEC.stYZ (BSCvsBEC.pscVec ω) P) ∧
    tauQ ⊤ q θ = -Real.logb q (1 - qscP q (Real.cos θ)) := by sorry

end BSCvsBEC.Supplement
