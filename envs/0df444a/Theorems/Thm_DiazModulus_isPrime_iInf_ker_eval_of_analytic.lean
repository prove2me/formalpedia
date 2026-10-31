-- Prove2me | Theorems.Thm_DiazModulus_isPrime_iInf_ker_eval_of_analytic
-- name    : DiazModulus.isPrime_iInf_ker_eval_of_analytic
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-30T09:52:01.505107+00:00
-- url     : https://prove2.me/theorems/cf445b01-0da9-4682-b381-833e8a341b35
-- title:
--   The polynomials vanishing on the image of an analytic map $F : E \to \mathbb{C}^\sigma$ from a normed $\mathbb{C}$-space form a prime ideal
-- statement:
--   Let $E$ be a normed space over $\mathbb{C}$, $\sigma$ a type and $F : E \to \mathbb{C}^\sigma$ a map each of whose coordinates $e \mapsto F(e)_i$ is analytic on all of $E$. Then the polynomials of $\mathbb{C}[X_\sigma]$ vanishing at every point $F(e)$, $e \in E$ (the ideal $\bigcap_{e} \ker \mathrm{eval}_{F(e)}$), form a prime ideal.
--
--   **Proof.** The ideal does not contain $1$. If $fg$ vanishes on the image while $f(F(e_0)) \ne 0$, then $g \circ F$ vanishes near $e_0$, and the identity theorem on the connected space $E$ makes it vanish everywhere.
--
--   **Novelty.** Classical; routine formalisation.
-- source:
--   Classical complex analysis: the identity theorem for analytic functions on a connected normed space. C1.3 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 30 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

theorem isPrime_iInf_ker_eval_of_analytic {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → σ → ℂ) (hF : ∀ i, AnalyticOnNhd ℂ (fun e => F e i) Set.univ) :
    (⨅ e : E, RingHom.ker (MvPolynomial.eval (F e))).IsPrime := by
  sorry

end DiazModulus
