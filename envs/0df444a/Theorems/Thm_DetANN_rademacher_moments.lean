-- Prove2me | Theorems.Thm_DetANN_rademacher_moments
-- name    : DetANN.rademacher_moments
-- status  : Proved
-- author  : @milia
-- created : 2026-11-15T17:41:27.526488+00:00
-- url     : https://prove2.me/theorems/05b0aaf7-9193-4f23-baa3-f9fbfce5c15d
-- title:
--   Moments of Rademacher sums via generating functions
-- statement:
--   Write $\mathrm{EGF}(m)=\sum_k m_kt^k/k!$ (definition `DetANN_SignChoice`).
--
--   1. Let $\sigma\in\{\pm1\}^n$ be uniform, $c\in\mathbb R$ and $a\in\mathbb R^n$. For every $m$,
--   $$\mathbb E\Bigl[\Bigl(c+\sum_r a_r\sigma_r\Bigr)^m\Bigr]=m!\,[t^m]\;e^{ct}\prod_r\cosh(a_rt).$$
--   2. Let $\Omega$ be a nonempty finite set, $\omega=(\omega_1,\dots,\omega_L)$ uniform in $\Omega^L$, and $X_\ell:\Omega\to\mathbb R$. For every $p$,
--   $$\mathbb E\Bigl[\Bigl(\sum_\ell X_\ell(\omega_\ell)\Bigr)^p\Bigr]=p!\,[t^p]\prod_\ell\mathrm{EGF}\bigl(k\mapsto\mathbb E[X_\ell(\omega_\ell)^k]\bigr).$$
--
--   These two identities compute the conditional moments in the proof of Lemma 6.2: part 1 for each coordinate $Y_{\ell,j,v}$ under a partial assignment, part 2 for the sum over the independent repetitions $\ell$.
--
--   **Formalization Note.** Expectations are uniform averages over finite sets (`avgOver`), and $[t^m]$ is the coefficient of a formal power series.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), proof of Lemma 6.2, p.16

import Mathlib
import Definitions.Def_DetANN_SignedBlocks
import Definitions.Def_DetANN_SignChoice

namespace DetANN

/-- **Moments of Rademacher sums via generating functions** (proof of Lemma 6.2).
1. For uniform signs `σ ∈ {±1}^n` and `Y = c + ∑_r a_r σ_r`,
   `E[Y^m] = m! [t^m] e^{ct} ∏_r cosh(a_r t)`.
2. If `X_1, …, X_L` depend on independent coordinates `ω_1, …, ω_L` of a uniform point of `Ω^L`,
   then `E[(∑_ℓ X_ℓ)^p] = p! [t^p] ∏_ℓ M_ℓ(t)`, where `M_ℓ` is the exponential generating function
   of the moments of `X_ℓ`. -/
theorem rademacher_moments :
    (∀ (n : ℕ) (c : ℝ) (a : Fin n → ℝ) (m : ℕ),
      avgOver (fun s : Fin n → Bool => (c + ∑ r, a r * signOf (s r)) ^ m) =
        (m.factorial : ℝ) * PowerSeries.coeff m (expSeries c * ∏ r, coshSeries (a r))) ∧
    ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] (L : ℕ) (X : Fin L → Ω → ℝ) (p : ℕ),
      avgOver (fun ω : Fin L → Ω => (∑ ℓ, X ℓ (ω ℓ)) ^ p) =
        (p.factorial : ℝ) * PowerSeries.coeff p (∏ ℓ, egf fun k => avgOver fun s => X ℓ s ^ k) := by
  sorry

end DetANN
