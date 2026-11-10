-- Prove2me | Theorems.Thm_DQILocal_Recon_lemma_4_1
-- name    : DQILocal.Recon.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:12.152306+00:00
-- url     : https://prove2.me/theorems/c5ca2113-e9b6-413c-ba55-36aacf6d496c
-- title:
--   Lemma 4.1 — node operations: a $y$-independent isometry at a symbol node, a block-diagonal check node
-- statement:
--   Let $q\ge2$ and let $\lambda,\mu$ be spectra (probability vectors on $\mathbb Z_q$).
--
--   1. **Symbol node.** There is an isometry $V:\mathbb C^q\to\mathbb C^q\otimes\mathbb C^q$, independent of $y$, with
--   $$V|\psi^{\lambda*\mu}_y\rangle=|\psi^\lambda_y\rangle|\psi^\mu_y\rangle\qquad\text{for all }y\in\mathbb Z_q .$$
--   2. **Check node.** For $y\in\mathbb Z_q$ let
--   $$\rho_y=\frac1q\sum_{y_1\in\mathbb Z_q}|\psi^\lambda_{y_1}\rangle\langle\psi^\lambda_{y_1}|\otimes|\psi^\mu_{y-y_1}\rangle\langle\psi^\mu_{y-y_1}|$$
--   be the state of two symbols with uniformly random values $y_1,y_2$ conditioned on $y_1+y_2=y$, and let $\Pi_\delta=\sum_{s-l=\delta}|s,l\rangle\langle s,l|$. Then $\rho_y=\sum_\delta\Pi_\delta\rho_y\Pi_\delta$; the probability $\operatorname{tr}(\Pi_\delta\rho_y)=P_{\lambda,\mu}(\delta)$ does not depend on $y$; and for every $\delta$ with $P_{\lambda,\mu}(\delta)>0$ there is an isometry $W_\delta$, independent of $y$, with
--   $$\frac{\Pi_\delta\rho_y\Pi_\delta}{P_{\lambda,\mu}(\delta)}=W_\delta|\psi^{\nu_\delta}_y\rangle\langle\psi^{\nu_\delta}_y|W_\delta^\dagger\qquad\text{for all }y .$$
--
--   Neither node operation loses information about the symbol values; this is what makes BPQM optimal on trees.
--
--   Differences from the source:
--   - encoding: two-qudit states and operators, ⊗, isometries → vectors and matrices indexed by ℤ_q × ℤ_q, Matrix.kroneckerMap, Vᴴ V = 1; reason: standard finite-dimensional encoding; same objects
--   - encoding: "independent of y", "does not depend on y" → quantifier order ∃ V ∀ y and ∀ δ ∃ W_δ ∀ y; tr(Π_δ ρ_y) equal to the y-free P_{λ,μ}(δ); reason: these are the same assertions
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Lemma 4.1, p. 23

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_Decoder

namespace DQILocal.Recon

open scoped BigOperators ComplexOrder

/-- **Lemma 4.1 (Node operations).**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Lemma 4.1, p. 23.
"Let `λ, μ` be spectra.
1. Symbol node. There is an isometry `V`, independent of `y`, with
   `V|ψ^{λ∗μ}_y⟩ = |ψ^λ_y⟩|ψ^μ_y⟩` for all `y`.
2. Check node. For `y ∈ ℤ_q` let
   `ρ_y = (1/q) Σ_{y₁} |ψ^λ_{y₁}⟩⟨ψ^λ_{y₁}| ⊗ |ψ^μ_{y-y₁}⟩⟨ψ^μ_{y-y₁}|` … For `δ ∈ ℤ_q` let
   `Π_δ = Σ_{s-l=δ} |s,l⟩⟨s,l|`. Then `ρ_y = Σ_δ Π_δ ρ_y Π_δ`, the probability
   `tr(Π_δ ρ_y) = P_{λ,μ}(δ)` does not depend on `y`, and, for every `δ` with `P_{λ,μ}(δ) > 0`,
   `Π_δ ρ_y Π_δ / P_{λ,μ}(δ) = W_δ |ψ^{ν_δ}_y⟩⟨ψ^{ν_δ}_y| W_δ†` for an isometry `W_δ` that does
   not depend on `y`."

**Formalization Note.** Two-qudit vectors and operators are indexed by `ℤ_q × ℤ_q` (first factor
`s`, second `l`); `|a⟩|b⟩` is `(s, l) ↦ a(s) b(l)` and `⊗` of operators is `Matrix.kroneckerMap`.
An isometry `V : ℂ^q → ℂ^q ⊗ ℂ^q` is `Vᴴ V = 1`. "Does not depend on `y`" is expressed by the
quantifier order (`∃ V, ∀ y`; `∀ δ, ∃ W_δ, ∀ y`) and by equality with the `y`-free `P_{λ,μ}(δ)`. -/
theorem lemma_4_1 {q : ℕ} [NeZero q] (hq : 2 ≤ q) (lam mu : ZMod q → ℝ) (hlam : IsProbVec lam)
    (hmu : IsProbVec mu) :
    let rho : ZMod q → Matrix (ZMod q × ZMod q) (ZMod q × ZMod q) ℂ := fun y =>
      (1 / (q : ℂ)) • ∑ y₁ : ZMod q,
        Matrix.kroneckerMap (· * ·)
          (Matrix.vecMulVec (psi lam y₁) (star (psi lam y₁)))
          (Matrix.vecMulVec (psi mu (y - y₁)) (star (psi mu (y - y₁))))
    let Pi : ZMod q → Matrix (ZMod q × ZMod q) (ZMod q × ZMod q) ℂ := fun δ =>
      Matrix.diagonal fun sl => if sl.1 - sl.2 = δ then 1 else 0
    (∃ V : Matrix (ZMod q × ZMod q) (ZMod q) ℂ, V.conjTranspose * V = 1 ∧
      ∀ y : ZMod q, V.mulVec (psi (conv lam mu) y) = fun sl => psi lam y sl.1 * psi mu y sl.2) ∧
    (∀ y : ZMod q, rho y = ∑ δ : ZMod q, Pi δ * rho y * Pi δ) ∧
    (∀ y δ : ZMod q, (Pi δ * rho y).trace = ((labelProb lam mu δ : ℝ) : ℂ)) ∧
    (∀ δ : ZMod q, 0 < labelProb lam mu δ →
      ∃ W : Matrix (ZMod q × ZMod q) (ZMod q) ℂ, W.conjTranspose * W = 1 ∧
        ∀ y : ZMod q,
          (1 / ((labelProb lam mu δ : ℝ) : ℂ)) • (Pi δ * rho y * Pi δ) =
            W * Matrix.vecMulVec (psi (nuDelta lam mu δ) y) (star (psi (nuDelta lam mu δ) y)) *
              W.conjTranspose) := by sorry

end DQILocal.Recon
