-- Prove2me | Theorems.Thm_DisruptReroute_GenEq_lemma_A_8
-- name    : DisruptReroute.GenEq.lemma_A_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:42.42298+00:00
-- url     : https://prove2.me/theorems/5f8fff7d-a5f9-4a9a-817a-d712d89a559a
-- title:
--   Lemma A.8, EC p. 12 — bounded and monotone cascade updates
-- statement:
--   The default update maps $\Phi^*$ and $\Psi^*$ have two properties. For every input profile, each output coordinate lies between zero and its original order. For feasible profiles with $\Gamma^B\le\Gamma^A$ and $\Delta^B\le\Delta^A$, both updates preserve that order:
--
--   $$0\le\Phi^*_{ij}{}^m(\Gamma,\Delta),\Psi^*_{ij}{}^m(\Gamma,\Delta)\le o^m_{ij},\qquad \Phi^*(\Gamma^B,\Delta^B)\le\Phi^*(\Gamma^A,\Delta^A),\quad\Psi^*(\Gamma^B,\Delta^B)\le\Psi^*(\Gamma^A,\Delta^A).$$
--
--   These bounds and monotonicity control the default cascade used in the general-equilibrium proposition.
--
--   **Formalization Note** The input bounds are needed for the monotonicity part because the inverse functions and market quantities are specified on the feasible order box. The update bounds hold for any real input profiles. The sentence immediately before Lemma A.8 says “decreasing,” but the lemma itself and p. 23 say “increasing.”
-- source:
--   Birge, Capponi & Chen, Disruption and Rerouting in Supply Chain Networks, SSRN 3669363 (version of October 31, 2022; Oper. Res. 2023, DOI 10.1287/opre.2022.2409), E-Companion, p. EC 12 (PDF p. 54), Lemma A.8

import Mathlib
import Definitions.Def_DisruptReroute_GenEq_Model

namespace DisruptReroute.GenEq

/-- Lemma A.8: boundedness and coordinatewise monotonicity of both updates. -/
theorem lemma_A_8 {N M : ℕ} (net : Network N M) (h : Standing net) :
    (∀ Γ Δ : Matrix N M, ∀ m i j,
      0 ≤ PhiStar net Γ Δ m i j ∧ PhiStar net Γ Δ m i j ≤ net.o m i j ∧
      0 ≤ PsiStar net Γ Δ m i j ∧ PsiStar net Γ Δ m i j ≤ net.o m i j) ∧
    (∀ ΓA ΓB ΔA ΔB : Matrix N M,
      InBounds net ΓA → InBounds net ΓB →
      InBounds net ΔA → InBounds net ΔB →
      ΓB ≤ ΓA → ΔB ≤ ΔA →
      PhiStar net ΓB ΔB ≤ PhiStar net ΓA ΔA ∧
      PsiStar net ΓB ΔB ≤ PsiStar net ΓA ΔA) := by sorry

end DisruptReroute.GenEq
