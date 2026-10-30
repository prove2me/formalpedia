-- Prove2me | Theorems.Thm_DigitalPrivacy_DataStrategy_theorem_1_optimal_data_strategy
-- name    : DigitalPrivacy.DataStrategy.theorem_1_optimal_data_strategy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:15:21.957141+00:00
-- url     : https://prove2.me/theorems/41643a50-5731-4f9a-8673-5e3ef20681e2
-- title:
--   Theorem 1 (corrected: $\psi>0$, (5) extended to $P\rho=0$, segment of optima on the knife-edge): optimal data collection and protection are (5)–(6), weakly increasing in $P$
-- statement:
--   Throughout, $\beta\in[0,1)$ is the strength of network effects and $\rho\in[0,1)$ the users' value of data (p. 6), $P\in[0,1]$ the business's revenue model and $\psi$ the unit cost of data protection (p. 8). Assume $\psi>0$. The business chooses $\xi\in[0,1]$ and $C\ge0$ to maximize $\Pi(\xi,C)=(1-P)\bar a^*+P\xi\bar a^*-\psi C$ at the subgame equilibrium activity $\bar a^*(\xi,C)$ of Proposition 1. Let
--
--   $$\xi^\star=\max\Big\{0,\min\Big\{1,\frac1{2P\rho}\Big(-(1-P)\rho-P+|P-(1-P)\rho|\sqrt{\frac{\psi}{\max\{0,\psi-P\rho\}}}\Big)\Big\}\Big\},\tag{5}$$
--   $$C^\star=\frac{\xi^\star}{1-\beta}\Big(-\xi^\star+\sqrt{\tfrac1\psi(1+\rho\xi^\star)(1-P(1-\xi^\star))}\Big).\tag{6}$$
--
--   Then:
--
--   1. $(\xi^\star,C^\star)$ is an optimal data strategy;
--   2. unless $P(1+\rho)=\rho$ and $\psi=P\rho$, it is the only one;
--   3. if $P(1+\rho)=\rho$ and $\psi=P\rho$, the optimal data strategies are exactly the points $(\xi,C_h(\xi))$, $\xi\in[0,1]$, with $C_h$ from Lemma 1;
--   4. with $\beta,\rho,\psi$ fixed, $P\mapsto\xi^\star$ and $P\mapsto C^\star$ are nondecreasing on $[0,1]$: a more data-driven business collects weakly more data and protects it weakly more.
--
--   In (5), $\psi/\max\{0,\psi-P\rho\}$ is read as $+\infty$ when $\psi\le P\rho$ (so $\xi^\star=1$), and the factor $\frac1{2P\rho}(\cdots)$ is replaced at $P\rho=0$ by the root of the same equation (see the definition of $\xi_i$).
--
--   This is the paper's characterization of the business's data strategy: data collection and data protection are complements, and both rise as the business's revenue relies more on data.
--
--   Differences from the source:
--   - correction: ψ ≥ 0 (p. 8) → 0 < ψ; reason: C_h and (6) divide by ψ, and at ψ = 0 with P + ρ > 0 the profit has no maximizer: β = 0, ρ = P = 1/2, ψ = 0 gives Π(1, C) = 3C/(2(C + 1)), which tends to 3/2 = sup Π without reaching it
--   - correction: the factor 1/(2Pρ) in ξᵢ and in (5), undefined at P = 0 and at ρ = 0 → xiI: for Pρ = 0 the root (a² − 4ψ(1 − P))/(4aψ), a = P + (1 − P)ρ, of the same equation C_inv = C_h (linear there), and 0 when P = ρ = 0; reason: the literal formula with Lean's x/0 = 0 gives ξ* = 0 at β = 0, ρ = 1/2, P = 0, ψ = 1/100, where the optimum is ξ* = 1; the replacement is also the limit of the printed formula as Pρ → 0
--   - correction: (ξ*, C*) of (5)–(6) is the business's strategy for every parameter → on the knife-edge P(1 + ρ) = ρ, ψ = Pρ the optimal set is the segment {(ξ, C_h(ξ)) : ξ ∈ [0, 1]}, which contains (ξ*, C*) = (1, C_h(1)); reason: (5) reads 0·√(ψ/0) there, and C_h(ξ) = ξ/(ρ(1 − β)) with Π(ξ, C_h(ξ)) = (1 − P)/(1 − β) for every ξ: β = 0, ρ = 1/2, P = 1/3, ψ = 1/6 gives Π(ξ, 2ξ) = 2/3 on [0, 1]
--   - reading: ψ/max{0, ψ − Pρ} in (5) when ψ ≤ Pρ → +∞, i.e. ξ* = 1 (explicit branch of xiStar); reason: the proof: the max{0, ψ − Pρ} 'turns ξi into ∞ (and, thus guarantees that ξ⋆ = 1 is chosen)' (p. 31); Lean's x/0 = 0 would give 0
--   - reading: ā*(ξ, C) of (3), which is 0/0 at (ξ, C) = (0, 0) → abarStar = 1/(1 − β) at ξ = 0; reason: the proof assigns (0, 0) the profit π₀ = (1 − P)/(1 − β) (p. 30) and writes ā_c = lim ā*(ξ*, C*) = 1/(1 − β) (p. 32); 1/(1 − β) is (3) at ξ = 0 for every C > 0
--   - encoding: the business maximizes its profit given the users' and adversaries' equilibrium strategy profile (a*, v*) (p. 9) → profit evaluated at ā = abarStar, the closed form (3) of Proposition 1; reason: Proposition 1 (milestone proposition_1_subgame) proves that (3) is the unique subgame equilibrium for C > 0
--   - reading: the business's data collection ξ⋆ and data protection C⋆ are (5)–(6) → (ξ*, C*) is optimal, and off the knife-edge it is the unique optimal strategy; reason: a characterization of the business's choice is read as the exact set of maximizers
--   - reading: a more data-driven business (higher P) sets weakly higher ξ⋆ and C⋆, all else equal → MonotoneOn of P' ↦ xiStar ρ P' ψ and P' ↦ cStar β ρ P' ψ on [0, 1]; reason: the claim concerns the closed forms (5)–(6) with β, ρ, ψ fixed (App. A.3, p. 33)
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (April 2022 draft; SSRN 3459274), Theorem 1, displays (5)–(6), pp. 11–12 (PDF 12–13); proof App. A.2, pp. 29–31 (PDF 30–32) and App. A.3, p. 33 (PDF 34)

import Mathlib
import Definitions.Def_DigitalPrivacy_DataStrategy_IsBusinessOptimal
import Definitions.Def_DigitalPrivacy_DataStrategy_cH
import Definitions.Def_DigitalPrivacy_DataStrategy_xiStar
import Definitions.Def_DigitalPrivacy_DataStrategy_cStar

namespace DigitalPrivacy.DataStrategy

/-- **Theorem 1 (corrected: `ψ > 0`, (5) extended to `Pρ = 0`, the knife-edge `P(1 + ρ) = ρ`,
`ψ = Pρ` has a segment of optima): the optimal data collection and data protection are (5)–(6)
and weakly increase in `P`.**
Fainmesser, Galeotti, Momot, *Digital Privacy*, author manuscript (April 2022 draft; SSRN 3459274), Theorem 1, displays (5)–(6), pp. 11–12 (PDF 12–13); proof App. A.2, pp. 29–31
(PDF 30–32) and the last part of App. A.3, p. 33 (PDF 34): "The digital business's data
collection, ξ⋆ and data protection, C⋆ are: ξ⋆ = max{0, min{1, (1/(2Pρ))(−(1 − P)ρ − P +
|P − (1 − P)ρ| · √(ψ/max{0, ψ − Pρ}))}}, (5) C⋆ = (ξ⋆/(1 − β)) · (−ξ⋆ + √((1/ψ)(1 + ρξ⋆)(1 −
P(1 − ξ⋆)))). (6) All else equal, a more data-driven digital business (i.e., higher P) sets weakly
higher levels of data collection, ξ⋆ and data protection, C⋆."

Standing assumptions: `β ∈ [0, 1)`, `ρ ∈ [0, 1)` (p. 6), `P ∈ [0, 1]` (p. 8) and `ψ > 0`.
The business maximizes the profit (2) at the subgame outcome (3) of Proposition 1 over
`ξ ∈ [0, 1]`, `C ≥ 0` (`IsBusinessOptimal`). Then:

1. `(ξ*, C*)` of (5)–(6) is an optimal data strategy;
2. unless `P(1 + ρ) = ρ` and `ψ = Pρ`, it is the only one;
3. if `P(1 + ρ) = ρ` and `ψ = Pρ`, the optimal data strategies are exactly `(ξ, C_h(ξ))` for
   `ξ ∈ [0, 1]` (which contains `(ξ*, C*) = (1, C_h(1))`);
4. with `β, ρ, ψ` fixed, `P ↦ ξ*` and `P ↦ C*` are monotone (weakly increasing) on `[0, 1]`.

**Formalization Note.** Corrections and readings of the printed statement:
* `ψ > 0` replaces the page's `ψ ≥ 0` (p. 8): (6) divides by `ψ`, and at `ψ = 0` with `P + ρ > 0`
  the profit has no maximizer (`β = 0`, `ρ = P = 1/2`: `Π(1, C) = 3C/(2(C + 1)) → 3/2` unattained).
* (5) is `xiStar`: its `ψ/max{0, ψ − Pρ}` is read as `+∞` for `ψ ≤ Pρ` (so `ξ* = 1`), as the
  proof says (p. 31), and its `1/(2Pρ)` is replaced at `Pρ = 0` by the root of the same equation
  `C_inv = C_h` (see `xiI`); the literal formula with Lean's `x/0 = 0` would give `ξ* = 0` at
  `β = 0`, `ρ = 1/2`, `P = 0`, `ψ = 1/100`, where the optimum is `ξ* = 1`.
* On the knife-edge `P(1 + ρ) = ρ`, `ψ = Pρ` (5) reads `0·√(ψ/0)`, and the maximizer is not
  unique: `C_h(ξ) = ξ/(ρ(1 − β))` and `Π(ξ, C_h(ξ)) = (1 − P)/(1 − β)` for every `ξ ∈ [0, 1]`
  (`β = 0`, `ρ = 1/2`, `P = 1/3`, `ψ = 1/6`: `Π(ξ, 2ξ) = 2/3`). Item 3 states that set.
* "The business's ξ⋆, C⋆ are (5)–(6)" is read as items 1–3; "higher P sets weakly higher ξ⋆, C⋆"
  as item 4 about the closed forms, for `P` ranging over `[0, 1]`.
* `ā*(0, C) = 1/(1 − β)` (`abarStar`), the value of (3) for `C > 0` and the proof's value at
  `(0, 0)` (π₀, p. 30). -/
theorem theorem_1_optimal_data_strategy {β ρ P ψ : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hψ : 0 < ψ) :
    IsBusinessOptimal β ρ P ψ (xiStar ρ P ψ) (cStar β ρ P ψ) ∧
    (¬ (P * (1 + ρ) = ρ ∧ ψ = P * ρ) →
      ∀ ξ C : ℝ, IsBusinessOptimal β ρ P ψ ξ C ↔ ξ = xiStar ρ P ψ ∧ C = cStar β ρ P ψ) ∧
    (P * (1 + ρ) = ρ ∧ ψ = P * ρ →
      ∀ ξ C : ℝ, IsBusinessOptimal β ρ P ψ ξ C ↔ ξ ∈ Set.Icc (0 : ℝ) 1 ∧ C = cH β ρ P ψ ξ) ∧
    MonotoneOn (fun P' => xiStar ρ P' ψ) (Set.Icc 0 1) ∧
    MonotoneOn (fun P' => cStar β ρ P' ψ) (Set.Icc 0 1) := by sorry

end DigitalPrivacy.DataStrategy
