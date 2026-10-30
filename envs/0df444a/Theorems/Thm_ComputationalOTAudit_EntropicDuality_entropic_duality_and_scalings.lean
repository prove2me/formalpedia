-- Prove2me | Theorems.Thm_ComputationalOTAudit_EntropicDuality_entropic_duality_and_scalings
-- name    : ComputationalOTAudit.EntropicDuality.entropic_duality_and_scalings
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:32:29.669737+00:00
-- url     : https://prove2.me/theorems/71f13556-1114-4372-9037-d5e87b6c7093
-- title:
--   Proposition 4.4 — Entropic duality and optimal scalings (corrected: zero bins)
-- statement:
--   Let $n,m>0$, let $a\in\Sigma_n$ and $b\in\Sigma_m$ be nonnegative probability histograms, let $C\in\mathbb R^{n\times m}$ be any real matrix, and let $\varepsilon>0$. Set $K_{ij}=e^{-C_{ij}/\varepsilon}$, $F(P)=\langle C,P\rangle-\varepsilon H(P)$ with $H(P)=-\sum_{ij}h(P_{ij})$, $h(0)=0$, and $h(t)=t(\log t-1)$ for $t>0$. Define $L=\inf_{P\in U(a,b)}F(P)$ independently of the dual. Write $I=\{i:a_i>0\}$ and $J=\{j:b_j>0\}$. The unrestricted dual is
--
--   $$Q(f,g)=\sum_i f_i a_i+\sum_j g_j b_j-\varepsilon\sum_{ij}e^{f_i/\varepsilon}K_{ij}e^{g_j/\varepsilon},$$
--
--   and $Q_{I,J}$ uses the same formula with every sum restricted to the positive supports. The coupling set, both supports, the primal value set, and the full dual value set are nonempty; the primal values are bounded below and the full dual values bounded above. There exist a unique primal optimizer $P^*$ and maximizing support potentials $f^*,g^*$ with
--
--   $$F(P^*)=L=\sup_{f\in\mathbb R^n,g\in\mathbb R^m}Q(f,g)=Q_{I,J}(f^*,g^*).$$
--
--   Every maximizing support pair has value $L$. Its exponentials on $I,J$, extended by zero to all original indices, are nonnegative scalings representing $P^*_{ij}=u_iK_{ij}v_j$ everywhere. Conversely every nonnegative representation of $P^*$ is positive exactly on $I,J$; its support logarithms $(\varepsilon\log u,\varepsilon\log v)$ maximize $Q_{I,J}$, and support exponentiation with zero extension returns the entire original pair. Every feasible nonnegative scaling yields $P^*$ and is primal optimal.
--
--   The full real dual has a maximizing pair if and only if every coordinate of both histograms is positive. Every full maximizer has value $L$ and its full exponentials represent $P^*$. When both histograms have full support, every nonnegative representation of $P^*$ is strictly positive, its full logarithms maximize $Q$, and full exponentiation returns that pair. Potential and scaling pairs are not asserted unique.
--
--   This is the complete value and optimizer correspondence of Proposition 4.4 with the necessary boundary correction; it requires no supplied optimum, duality certificate, or algorithmic convergence hypothesis.
--
--   Differences from the source:
--   - correction: (4.30) prints a finite-real maximum and (4.31) finite exponentials for every histogram → an attained support maximum, the exact full-real supremum, zero-extended scaling correspondence in both directions, and full-real attainment exactly at full support; reason: for n=2, m=1, a=(1,0), b=(1), C=0 and epsilon=1 the unique coupling is (1,0), the primal value is -1, but Q=x-exp(x)-exp(y)<-1 for every finite x,y and tends to -1 with x=0 and y tending to minus infinity.
--   - reading: the vector convention after (4.1), printed p. 425, assigns minus infinity at zero while the raw matrix formula leaves log zero undefined → continuous shifted matrix entropy with h(0)=0 and h(t)=t(log(t)-1) for t>0; reason: the proof on printed p. 426 uses continuity and Example 8.1 (8.4), printed p. 495, gives the corresponding KL scalar value 1 at zero; the admissible coupling (1,0) otherwise makes the primal infinite or undefined.
--   - encoding: one-based finite indices, implicit finite extremal values, and the optimizer/scaling link in (4.12) and (4.31) → Fin n and Fin m, positive-support subtypes, zero extension, explicit nonempty and bounded value sets, unique primal attainment, and quantified forward and inverse optimizer correspondences; reason: all original histogram and cost instances are retained; real infimum and supremum defaults cannot replace the values, and logarithms occur in inverse claims only where the scaling coordinates are asserted positive.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport, Foundations and Trends in Machine Learning 11(5–6):355–607, 2019, DOI 10.1561/2200000073, Proposition 4.4, (4.30)–(4.31), printed p. 448 / PDF p. 98; proof continues printed p. 449 / PDF p. 99. Prerequisite Proposition 4.3 (4.12), printed p. 432 / PDF p. 82. Entropy reading: (4.1) and continuity, printed pp. 425–426 / PDF pp. 75–76; Example 8.1 (8.4), printed p. 495 / PDF p. 145. https://doi.org/10.1561/2200000073

import Mathlib
import Definitions.Def_ComputationalOTAudit_EntropicDuality_support_interface

namespace ComputationalOTAudit.EntropicDuality

/-- Proposition 4.4, (4.30)–(4.31), printed pp. 448–449 / PDF pp. 98–99.
Corrected: zero bins require a full supremum and an attained support maximum.
For a=(1,0), b=(1), C=0, ε=1, L=-1 while Q=x-exp(x)-exp(y)<-1
for every finite x,y. Entropy uses the continuous matrix reading at zero,
as in the continuity argument on p. 426 and Example 8.1 on p. 495.
Both the value identity and the complete exponential/logarithmic correspondence
are retained; no optimizer, boundedness or duality certificate is a hypothesis. -/
theorem entropic_duality_and_scalings {n m : ℕ}
    (C : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hε : 0 < ε)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    (CompOT.Assignment.couplings a b).Nonempty ∧
    (PrimalValues C a b ε).Nonempty ∧ BddBelow (PrimalValues C a b ε) ∧
    (FullDualValues C a b ε).Nonempty ∧ BddAbove (FullDualValues C a b ε) ∧
    Nonempty (PositiveSupport a) ∧ Nonempty (PositiveSupport b) ∧
    ∃ P : Matrix (Fin n) (Fin m) ℝ,
      CompOT.EntropicLimit.IsEntropicOptimal C a b ε P ∧
      (∀ R, CompOT.EntropicLimit.IsEntropicOptimal C a b ε R → R = P) ∧
      CompOT.EntropicLimit.entObjective C ε P = PrimalValue C a b ε ∧
      PrimalValue C a b ε = sSup (FullDualValues C a b ε) ∧
      (∃ f : PositiveSupport a → ℝ, ∃ g : PositiveSupport b → ℝ,
        IsSupportDualMaximizer C a b ε f g ∧
        SupportDualObjective C a b ε f g = PrimalValue C a b ε) ∧
      (∀ (f : PositiveSupport a → ℝ) (g : PositiveSupport b → ℝ),
        IsSupportDualMaximizer C a b ε f g →
          SupportDualObjective C a b ε f g = PrimalValue C a b ε ∧
          RepresentsCoupling C ε P (SupportExp a ε f) (SupportExp b ε g)) ∧
      (∀ (u : Fin n → ℝ) (v : Fin m → ℝ), RepresentsCoupling C ε P u v →
        (∀ i, 0 < u i ↔ 0 < a i) ∧ (∀ j, 0 < v j ↔ 0 < b j) ∧
        IsSupportDualMaximizer C a b ε (SupportLog a ε u) (SupportLog b ε v) ∧
        SupportExp a ε (SupportLog a ε u) = u ∧
        SupportExp b ε (SupportLog b ε v) = v) ∧
      (∀ (u : Fin n → ℝ) (v : Fin m → ℝ), IsFeasibleScaling C a b ε u v →
        ScaledCoupling C ε u v = P ∧
        CompOT.EntropicLimit.IsEntropicOptimal C a b ε (ScaledCoupling C ε u v)) ∧
      ((∃ f : Fin n → ℝ, ∃ g : Fin m → ℝ, IsFullDualMaximizer C a b ε f g) ↔
        FullSupport a ∧ FullSupport b) ∧
      (∀ (f : Fin n → ℝ) (g : Fin m → ℝ), IsFullDualMaximizer C a b ε f g →
        CompOT.EntropicDual.dualObjEnt C a b ε f g = PrimalValue C a b ε ∧
        RepresentsCoupling C ε P (FullExp ε f) (FullExp ε g)) ∧
      (FullSupport a ∧ FullSupport b →
        ∀ (u : Fin n → ℝ) (v : Fin m → ℝ), RepresentsCoupling C ε P u v →
          (∀ i, 0 < u i) ∧ (∀ j, 0 < v j) ∧
          IsFullDualMaximizer C a b ε (FullLog ε u) (FullLog ε v) ∧
          FullExp ε (FullLog ε u) = u ∧ FullExp ε (FullLog ε v) = v) := by sorry

end ComputationalOTAudit.EntropicDuality
