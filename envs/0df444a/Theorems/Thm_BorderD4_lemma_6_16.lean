-- Prove2me | Theorems.Thm_BorderD4_lemma_6_16
-- name    : BorderD4.lemma_6_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:01:57.119732+00:00
-- url     : https://prove2.me/theorems/ac76c0b5-12af-4072-960c-3d23393d9aa0
-- title:
--   Lemma 6.16: derivatives of $\Psi(p)$ and growth of $\Sigma\Pi\Psi$
-- statement:
--   In the situation of §6.3, for every $p\in F[[\varepsilon]][x]$,
--   $$z\,\partial_z\Psi(p)=\Psi(Dp)-\sum_{a\notin T}\Psi(\partial_a p)\cdot\Psi(DQ_a)\cdot\Psi(\partial_a Q_a)^{-1}.$$
--   Consequently:
--
--   1. $\partial_z\,\Sigma\Pi\Psi(m,\ell)\subseteq\Sigma\Pi\Psi((1+(k+1)\ell)m,\ell+4)$;
--   2. $\mathrm{dlog}_z(U/V)\in\Sigma\Pi\Psi((k+1)\rho,4)$ for all $U,V\in\Pi\Psi(P)$.
--
--   The chain rule keeps every series a single factor, so the differentiation steps never need to expand it.
--
--   Differences from the source:
--   - generalization: §6 fixes $N=(k+1)n$ (p.49) → an arbitrary finite nonempty index type; reason: the proof uses $N$ only as the number of variables; $\mathrm{Fin}(k+1)\times\mathrm{Fin}\,n$ is the source
--   - generalization: $f$ border computed by the circuit of §6.3 (p.62), with the form of Theorem 6.7 → any `LowWeightForm` of any polynomial $f$, with no circuit in the data; reason: §6.3 uses only that form (26)–(27); the form Theorem 6.7 produces is an instance
--   - encoding: the field $K=L((\varepsilon))$, $L=F(u)((z))$ (p.65) → the fraction field of $F[[\varepsilon]][u][[z]]$, with $\partial_z$ by the quotient rule; reason: it embeds in $K$ compatibly with inverses and $\partial_z$, and contains every series used
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 6.16, p.68

import Mathlib
import Definitions.Def_BorderD4_LowWeightForm
import Definitions.Def_BorderD4_SigmaPiPsi
import Definitions.Def_BorderD4_zDeriv
import Definitions.Def_BorderD4_eulerD
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- Lemma 6.16, derivatives: in the situation of §6.3, for every `p ∈ F[[ε]][x]`,
`z ∂_z Ψ(p) = Ψ(Dp) − ∑_{a∉T} Ψ(∂_a p) · Ψ(DQ_a) · Ψ(∂_a Q_a)⁻¹` (30), and consequently
(1) `∂_z ΣΠΨ(m, ℓ) ⊆ ΣΠΨ((1 + (k + 1)ℓ)m, ℓ + 4)`, and (2) `dlog_z(U/V) ∈ ΣΠΨ((k + 1)ρ, 4)` for all `U, V ∈ ΠΨ(P)`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Lemma 6.16, p.68.

**Formalization Note** The situation of §6.3 is a `LowWeightForm`, `Δ = δ^k`, and `P` is its set `factors`. (30) is
stated in the fraction field with the left side in the ring, where `∂_z` is `PowerSeries.derivative`. -/
theorem lemma_6_16 {F σ : Type*} [Field F] [IsAlgClosed F] [CharZero F] [Fintype σ] [DecidableEq σ]
    [Nonempty σ] {f : MvPolynomial σ F} {k δ ρ : ℕ} (_hk : 1 ≤ k) (_hδ : 1 ≤ δ) (_hρ : 1 ≤ ρ)
    (D : LowWeightForm f k δ ρ) :
    (∀ p : MvPolynomial σ F⟦X⟧,
      algebraMap (ZRing F D.T) (ZFrac F D.T)
          (PowerSeries.X * PowerSeries.derivative _ (Psi D.T D.φ p)) =
        PsiF D.T D.φ (eulerD D.T p) -
          ∑ a : {a // a ∉ D.T}, PsiF D.T D.φ (pderiv a.1 p) * PsiF D.T D.φ (eulerD D.T (D.Q a)) *
            (PsiF D.T D.φ (pderiv a.1 (D.Q a)))⁻¹) ∧
    (∀ m ℓ : ℕ, 1 ≤ m → ∀ A ∈ SigmaPiPsi D.T D.φ (δ ^ k) m ℓ,
      zDeriv A ∈ SigmaPiPsi D.T D.φ (δ ^ k) ((1 + (k + 1) * ℓ) * m) (ℓ + 4)) ∧
    (∀ U' V' : ZFrac F D.T, U' ∈ PiPsi D.T D.φ (D.factors : Set (MvPolynomial σ F⟦X⟧)) →
      V' ∈ PiPsi D.T D.φ (D.factors : Set (MvPolynomial σ F⟦X⟧)) →
      dlogZ (U' / V') ∈ SigmaPiPsi D.T D.φ (δ ^ k) ((k + 1) * ρ) 4) := by sorry

end BorderD4
