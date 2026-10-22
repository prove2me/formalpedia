-- Prove2me | Theorems.Thm_ChannelRandomization_PostProc_theorem_3
-- name    : ChannelRandomization.PostProc.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:28.382172+00:00
-- url     : https://prove2.me/theorems/885aa2cd-35b9-4dec-8f7c-c5095adf539d
-- title:
--   Theorem 3, p. 15 — post-processing randomization theorem: Ψ ⪰_{ε,D} Φ ⟺ (ii) ⟺ (iii) ⟺ (iv); with id ∈ P, ⪰_ε ⟺ ⪰_{ε,B}
-- statement:
--   Fix an admissible family $\mathcal P$ of positive cones. Let $\mathcal A,\mathcal B,\mathcal B',\mathcal D$ be C*-algebras, $\Phi\in\mathcal C(\mathcal A,\mathcal B)$ and $\Psi\in\mathcal C(\mathcal A,\mathcal B')$ two $\mathcal P$-channels with the same input, and $\epsilon\ge0$. The following are equivalent:
--
--   1. $\Psi\succeq_{\epsilon,\mathcal D}\Phi$: for every $\Gamma\in\mathcal P^*(\mathcal D,\mathcal A)$ and every $\alpha\in\mathcal C(\mathcal B,\mathcal D)$ there is $\alpha'\in\mathcal C(\mathcal B',\mathcal D)$ with $\langle\alpha\circ\Phi,\Gamma\rangle\le\langle\alpha'\circ\Psi,\Gamma\rangle+\epsilon\|\Gamma\|^\diamond$;
--   2. for every $\Gamma\in\mathcal P^*(\mathcal D,\mathcal A)$, $$\|\Phi\circ\Gamma\|^\diamond\le\|\Psi\circ\Gamma\|^\diamond+\epsilon\|\Gamma\|^\diamond ;$$
--   3. for every $\Gamma\in\mathcal L(\mathcal D,\mathcal A)$ and every $\alpha\in\mathcal C(\mathcal B,\mathcal D)$ there is $\alpha'\in\mathcal C(\mathcal B',\mathcal D)$ with $$\langle\alpha\circ\Phi,\Gamma\rangle\le\langle\alpha'\circ\Psi,\Gamma\rangle+2\epsilon\|\Gamma\|^\diamond ;$$
--   4. for every $\alpha\in\mathcal C(\mathcal B,\mathcal D)$ there is $\alpha'\in\mathcal C(\mathcal B',\mathcal D)$ with $$\|\alpha\circ\Phi-\alpha'\circ\Psi\|_\diamond\le2\epsilon .$$
--
--   Moreover, if the identity maps belong to $\mathcal P$, then $\Psi\succeq_\epsilon\Phi$ (deficiency for every decision algebra $\mathcal D$) if and only if $\Psi\succeq_{\epsilon,\mathcal B}\Phi$.
--
--   Here $\|\cdot\|_\diamond$ and $\|\cdot\|^\diamond$ are the norms (5) and (7) built from $\mathcal P$; the norm in (ii) of $\Phi\circ\Gamma\in\mathcal L(\mathcal D,\mathcal B)$ is taken in $\mathcal L(\mathcal D,\mathcal B)$, and in (iv) the difference lies in $\mathcal L(\mathcal A,\mathcal D)$. This is the quantum, channel-level analogue of the Blackwell–Le Cam randomization theorem: approximate dominance in every post-processing decision problem is equivalent to the existence of approximate post-processings in the diamond norm, and for $\mathcal P\supseteq CP$ the single decision algebra $\mathcal D=\mathcal B$ suffices.
--
--   **Formalization Note.** The equivalence is stated as `List.TFAE` of the four conditions, conjoined with the Moreover clause; "id ∈ P" is read as: the identity map of $B(\mathbb C^n)$ lies in $\mathcal P(\mathbb C^n,\mathbb C^n)$ for every $n$. Decision algebras range over all block-label algebras, including the classical $\mathbb D_n$ and full matrix algebras.
-- source:
--   Jenčová, Randomization theorems for quantum channels, arXiv:1404.3900v1, p. 15, Theorem 3 (standing data from §3.2, p. 14, and Definition 3, pp. 14–15)

import Mathlib
import Definitions.Def_ChannelRandomization_PostProc_Setting

namespace ChannelRandomization.PostProc
theorem theorem_3 (P : AdmissibleFamily) {a b b' d : ℕ} (A : Fin a → ℕ) (B : Fin b → ℕ)
    (B' : Fin b' → ℕ) (D : Fin d → ℕ)
    (Φ : Map a b) (Ψ : Map a b') (hΦ : Φ ∈ channels P A B) (hΨ : Ψ ∈ channels P A B')
    (ε : ℝ) (hε : 0 ≤ ε) :
    List.TFAE
      [PostDeficientIn P ε A B B' D Φ Ψ,
       ∀ Γ ∈ dualCone P D A,
         dualDiamond P D B (Φ ∘ₗ Γ) ≤ dualDiamond P D B' (Ψ ∘ₗ Γ) + ε * dualDiamond P D A Γ,
       ∀ Γ : Map d a, InL D A Γ → ∀ α ∈ channels P B D, ∃ α' ∈ channels P B' D,
         pair (α ∘ₗ Φ) Γ ≤ pair (α' ∘ₗ Ψ) Γ + 2 * ε * dualDiamond P D A Γ,
       ∀ α ∈ channels P B D, ∃ α' ∈ channels P B' D,
         diamond P A D (α ∘ₗ Φ - α' ∘ₗ Ψ) ≤ 2 * ε] ∧
    ((∀ n : ℕ, (LinearMap.id : Map n n) ∈ P.cone n n) →
      (PostDeficient P ε A B B' Φ Ψ ↔ PostDeficientIn P ε A B B' B Φ Ψ)) := by sorry
end ChannelRandomization.PostProc
