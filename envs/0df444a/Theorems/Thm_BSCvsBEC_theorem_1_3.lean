-- Prove2me | Theorems.Thm_BSCvsBEC_theorem_1_3
-- name    : BSCvsBEC.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:41:18.978776+00:00
-- url     : https://prove2.me/theorems/844ebec9-5def-4a3d-b42f-76adaa5539ed
-- title:
--   Theorem 1.3: $\mathrm{PSC}_\theta$ is more capable than $\mathrm{BEC}_\lambda$ iff $\lambda\ge\cos^2\theta$
-- statement:
--   Let $0\le\theta\le\pi/2$, $0\le\lambda\le1$, and let $|\omega_0\rangle,|\omega_1\rangle\in\mathbb C^2$ be unit vectors with $\langle\omega_0|\omega_1\rangle=\cos\theta$, defining the pure state channel $\mathrm{PSC}_\theta$. For every block length $n\ge1$, the inequality
--   $$H(X\mid\mathrm{PSC}_\theta(X))\ \le\ H(X\mid\mathrm{BEC}_\lambda(X))$$
--   holds for every random variable $X$ on $\mathbb F_2^n$ if and only if
--   $$\lambda\ \ge\ \cos^2\theta.$$
--   Both conditional entropies are $H(XY)-H(Y)$ in bits: of the classical–quantum state $\sum_xP_X(x)|x\rangle\langle x|\otimes|\omega_x\rangle\langle\omega_x|$ for the pure state channel, and of the joint distribution of $X$ and its coordinatewise erasure for $\mathrm{BEC}_\lambda$.
--
--   In the language of Körner and Marton: $\mathrm{PSC}_\theta$ is more capable than $\mathrm{BEC}_\lambda$ exactly when $\lambda\ge\cos^2\theta$. In particular, for every random $X$ on $\mathbb F_2^n$, $H(X\mid\mathrm{PSC}_\theta(X))\le H(X\mid\mathrm{BEC}_{\cos^2\theta}(X))$.
--
--   Differences from the source:
--   - reading: 'PSC_θ is more capable than BEC_λ' (single-letter, p.2) and 'for every random variable X on F₂ⁿ' (n-letter) → for each fixed n ≥ 1: (∀ pmf P on F₂ⁿ, H(X|PSC_θ(X)) ≤ H(X|BEC_λ(X))) ↔ cos²θ ≤ λ; reason: n = 1 is the single-letter relation and ∀ n gives the n-letter form; n = 0 is excluded because both entropies vanish there
--   - reading: some fixed pure states |ω₀⟩, |ω₁⟩ with ⟨ω₀|ω₁⟩ = cos θ → every pair of unit vectors in ℂ² with inner ω₀ ω₁ = cos θ; reason: the page fixes an arbitrary such pair; the statement is required for each one
--   - encoding: PSC_θ for 0 ≤ θ ≤ π/2 and BEC_λ → hypotheses 0 ≤ θ ≤ π/2 and 0 ≤ λ ≤ 1; reason: the ranges on which the paper defines the channels (p.5)
--   - encoding: a random variable X on a finite set → its pmf P with IsPMF P; reason: Lean convention; same instances
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Theorem 1.3, eq. (14), p.4; 'more capable' p.2; channels and entropies §2.1, pp.5–6

import Mathlib
import Definitions.Def_BSCvsBEC_shannon
import Definitions.Def_BSCvsBEC_condEntBEC
import Definitions.Def_BSCvsBEC_condEntPSC

namespace BSCvsBEC

/-- **Theorem 1.3 (p.4).** `PSC_θ` is more capable than `BEC_λ` if and only if `λ ≥ cos²θ`.
Equivalently, for every random variable `X` on `F₂ⁿ`, `H(X | PSC_θ(X)) ≤ H(X | BEC_{cos²θ}(X))`
(eq. (14)).
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Theorem 1.3, p.4 ("more capable": p.2; channels: §2.1, p.5).

**Formalization Note.** For every `θ ∈ [0, π/2]`, `λ ∈ [0, 1]`, every pair of unit vectors `ω₀, ω₁ ∈ ℂ²`
with `⟨ω₀|ω₁⟩ = cos θ`, and every block length `n ≥ 1`: the inequality
`H(X | PSC_θ(X)) ≤ H(X | BEC_λ(X))` holds for every pmf on `F₂ⁿ` iff `cos²θ ≤ λ`. Taking `n = 1` gives
the single-letter "more capable" relation, and all `n` give the `n`-letter form (14). Conditional
entropies are `H(XY) − H(Y)` of the joint distribution/state, in bits. -/
theorem theorem_1_3 (θ lam : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) (ω : Fin 2 → EuclideanSpace ℂ (Fin 2)) (hω : IsPSCPair θ ω)
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ P : (Fin n → Fin 2) → ℝ, IsPMF P → condEntPSC ω P ≤ condEntBEC lam P) ↔
      Real.cos θ ^ 2 ≤ lam := by sorry

end BSCvsBEC
