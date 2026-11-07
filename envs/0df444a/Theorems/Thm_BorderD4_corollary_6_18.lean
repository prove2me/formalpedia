-- Prove2me | Theorems.Thm_BorderD4_corollary_6_18
-- name    : BorderD4.corollary_6_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:02:18.668975+00:00
-- url     : https://prove2.me/theorems/8d515569-83d1-48f2-b94f-5cb96d711385
-- title:
--   Corollary 6.18: coefficients of $\Sigma\Pi\Psi(m,\ell)$ lie in $C_\Delta(m,r)$
-- statement:
--   In the situation of §6.3, let $A\in\Sigma\Pi\Psi(m,\ell)$ and $r:=(\ell+k)(\Delta+1)^{k+1}$. Then:
--
--   1. for every $d\in\mathbb Z$, $[z^d]A\in C_\Delta(m,r;F((\varepsilon)))$;
--   2. if $A\ne 0$ and $\tilde A$ is its normalization, then $\mathrm{tc}(\lim\tilde A)\in\overline{C}_\Delta(m,r)$.
--
--   The arity $r$ does not depend on $d$, which is what makes the class usable.
--
--   Differences from the source:
--   - generalization: §6 fixes $N=(k+1)n$ (p.49) → an arbitrary finite nonempty index type; reason: the proof uses $N$ only as the number of variables; $\mathrm{Fin}(k+1)\times\mathrm{Fin}\,n$ is the source
--   - generalization: $f$ border computed by the circuit of §6.3 (p.62), with the form of Theorem 6.7 → any `LowWeightForm` of any polynomial $f$, with no circuit in the data; reason: §6.3 uses only that form (26)–(27); the form Theorem 6.7 produces is an instance
--   - encoding: the field $K=L((\varepsilon))$, $L=F(u)((z))$ (p.65) → the fraction field of $F[[\varepsilon]][u][[z]]$, with $\partial_z$ by the quotient rule; reason: it embeds in $K$ compatibly with inverses and $\partial_z$, and contains every series used
--   - encoding: $[z^d]A$ and $\mathrm{tc}(\lim\tilde A)$ → `zCoeffOf` and `IsTrailingLimit` on a representation $A=\varepsilon^{-c}z^{-b}h$, whose existence is part of the conclusion; reason: $\Sigma\Pi\Psi(m,\ell)\subseteq S$ (p.67), and these values do not depend on the representation
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Corollary 6.18, p.70

import Mathlib
import Definitions.Def_BorderD4_LowWeightForm
import Definitions.Def_BorderD4_SigmaPiPsi
import Definitions.Def_BorderD4_CompClass
import Definitions.Def_BorderD4_BorderCompClass
import Definitions.Def_BorderD4_IsTrailingLimit
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- Corollary 6.18: in the situation of §6.3, let `A ∈ ΣΠΨ(m, ℓ)` and `r := (ℓ + k)(Δ + 1)^{k+1}`. (1) For every `d ∈ ℤ`,
`[z^d]A ∈ C_Δ(m, r; F((ε)))`. (2) If `A ≠ 0` and `Ã` is its normalization, then `tc(lim Ã)` lies in the border class
`C̄_Δ(m, r)`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Corollary 6.18, p.70.

**Formalization Note** `[z^d]A` is taken through a representation `A = ε^{−c} z^{−b} h` in `F[[ε]][u][[z]]_{εz}`, whose
existence is asserted (p.67). `tc(lim Ã)` is `IsTrailingLimit`. -/
theorem corollary_6_18 {F σ : Type*} [Field F] [IsAlgClosed F] [CharZero F] [Fintype σ]
    [DecidableEq σ] [Nonempty σ] {f : MvPolynomial σ F} {k δ ρ : ℕ} (_hk : 1 ≤ k) (_hδ : 1 ≤ δ)
    (_hρ : 1 ≤ ρ) (D : LowWeightForm f k δ ρ) {m ℓ : ℕ} (_hm : 1 ≤ m) (A : ZFrac F D.T)
    (hA : A ∈ SigmaPiPsi D.T D.φ (δ ^ k) m ℓ) :
    (∃ (c b : ℕ) (h : ZRing F D.T), IsZRep A c b h ∧ ∀ d : ℤ,
      zCoeffOf c b h d ∈
        CompClass (LaurentSeries F) D.T (δ ^ k) m ((ℓ + k) * (δ ^ k + 1) ^ (k + 1))) ∧
    (A ≠ 0 → ∃ G : MvPolynomial D.T F, IsTrailingLimit A G ∧
      G ∈ BorderCompClass F D.T (δ ^ k) m ((ℓ + k) * (δ ^ k + 1) ^ (k + 1))) := by sorry

end BorderD4
