-- Prove2me | Theorems.Thm_BlockchainMarketPower_psi_star
-- name    : BlockchainMarketPower.psi_star
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:27:01.35798+00:00
-- url     : https://prove2.me/theorems/962bb051-7b7c-41ad-83e7-789ea857b5c2
-- title:
--   Proposition 3.1 part 3: $\Psi^\star$ and $\Lambda$ (corrected: unique on $(0,P)$)
-- statement:
--   Let $\gamma\in(0,1)$, $n\ge1$ and $0<P\le1$. For every $\Psi$, the derivative of $\psi\mapsto f(P,\psi;\gamma/n)$ at $\Psi$ is $\Lambda(\Psi,P,n)$. Moreover there is a point $\Psi^\star\in(0,P)$ such that
--
--   1. $f(P,\Psi^\star;\gamma/n)>0$;
--   2. $\Psi^\star$ is the unique maximizer of $f(P,\cdot;\gamma/n)$ on $[0,P]$;
--   3. for $\Psi\in(0,P)$: $\Lambda(\Psi,P,n)=0$ if and only if $\Psi=\Psi^\star$.
--
--   Thus the equilibrium supplier price is well defined as the root of $\Lambda$ in $(0,P)$.
--
--   Differences from the source:
--   - correction: Ψ⋆ "is the unique solution" of Λ(Ψ⋆, P, N) = 0 → unique root of Λ(·, P, n) in (0, P); reason: Λ is a cubic with several real roots: at α = 3/4 (P = 1/2), γ = 1/2, N = 1, Λ(1, 1/2, 1) = -47/64 and Λ(3, 1/2, 1) = 69/64, so there is a root in (1, 3) besides the one in (0, 1/2); the proof on pp.35–36 says Ψ∗ ∈ (0, P∗)
--   - generalization: P = P⋆_NB with N = 1, P = P⋆_B with N → every P ∈ (0, 1] and every n ≥ 1; reason: the printed pairs are special cases
-- source:
--   Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, Proposition 3.1 part 3, p.19; proof pp.35–36, p.39

import Mathlib
import Definitions.Def_BlockchainMarketPower_Model

namespace BlockchainMarketPower

/-- The unique interior maximizer is the unique root of `Λ` in `(0, P)`,
Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, Proposition 3.1 part 3, pp.18–19, and proof pp.35–36, 39:
`Λ(·, P, n) = ∂f/∂Ψ` at `γ' = γ/n`, and there is `Ψ⋆ ∈ (0, P)` with `f(P, Ψ⋆; γ/n) > 0`, the unique
maximizer of `f(P, ·; γ/n)` on `[0, P]` and the unique root of `Λ(·, P, n)` in `(0, P)`.

**Formalization Note.** **Corrected:** the page says "the unique solution"; as an equation over the
reals this is false, because `Λ` is a cubic with several real roots. The proof (pp.35–36) has it right,
with `Ψ∗ ∈ (0, P∗)`. -/
theorem psi_star (γ P : ℝ) (n : ℕ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (hn : 1 ≤ n) (hP₀ : 0 < P)
    (hP₁ : P ≤ 1) :
    (∀ Ψ : ℝ, HasDerivAt (fun ψ => f P ψ (γ / (n : ℝ))) (Lam γ Ψ P n) Ψ) ∧
      ∃ Ψs ∈ Set.Ioo 0 P,
        0 < f P Ψs (γ / (n : ℝ)) ∧
        (∀ Ψ ∈ Set.Icc 0 P, Ψ ≠ Ψs → f P Ψ (γ / (n : ℝ)) < f P Ψs (γ / (n : ℝ))) ∧
        ∀ Ψ ∈ Set.Ioo 0 P, Lam γ Ψ P n = 0 ↔ Ψ = Ψs := by sorry

end BlockchainMarketPower
