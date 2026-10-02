-- Prove2me | Theorems.Thm_DiazModulus_candidate_log_mul_real_iff_rat_conj
-- name    : DiazModulus.candidate_log_mul_real_iff_rat_conj
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:44:14.029737+00:00
-- url     : https://prove2.me/theorems/63bbb69f-c091-429d-ae55-5c8a054c74a5
-- title:
--   For a candidate u and a logarithm μ algebraic over ℚ(u): uμ is real exactly when μ ∈ ℚū, and uμ is never purely imaginary
-- statement:
--   Let $u$ be a candidate for Diaz's conjecture (`DiazModulus.IsCandidate`: $u \neq 0$ with $|u|$ and $e^u$ algebraic), and let $\mu \neq 0$ be a logarithm of an algebraic number that is algebraic over $\mathbb{Q}[u]$. Then $u\mu$ is real if and only if $\mu = q\bar u$ for some $q \in \mathbb{Q}$, and $u\mu$ is never purely imaginary.
--
--   So among the logarithms algebraic over $\mathbb{Q}(u)$, the conjugate $\bar u$ is, up to a rational factor, the only one whose product with $u$ lies on an axis, whether or not that product is algebraic. Compare `DiazModulus.candidate_norm_div_log_not_log`, which concerns the factorisations of $|u|^2$ itself.
--
--   **Proof.** A candidate lies on neither axis: there $\bar u = \pm u$, so $u^2 = \pm|u|^2$ would be algebraic, against Hermite–Lindemann (`DiazModulus.hermite_lindemann_holds`). Since $\bar u = |u|^2/u$ with $|u|^2$ algebraic, $\bar u$ is algebraic over $\mathbb{Q}[u]$, and so is $\bar\mu$, which is algebraic over $\mathbb{Q}[\bar u]$. Hence $u, \mu, \bar u, \bar\mu$ generate an algebra of transcendence degree at most one (`Transcendence.trdeg_adjoin_le_one_of_isAlgebraic_adjoin`). If $u\mu$ is real, `DiazModulus.log_mul_real_trichotomy_of_trdeg_one` leaves only $\mu \in \mathbb{Q}\bar u$; conversely $u \cdot q\bar u = q|u|^2$ is real. If $u\mu$ were purely imaginary, `DiazModulus.log_mul_imaginary_mixed_of_trdeg_one` would put $u$ on an axis.
--
--   **Novelty.** Not asserted. In Diaz's reading of (Qr2) (2007, p. 377), $\mathbb{R}\ell \cap \mathcal{L} = \mathbb{Q}\ell$ and $i\mathbb{R}\ell \cap \mathcal{L} = \{0\}$; this node is that reading at $\ell = \bar u$, proved for the logarithms algebraic over $\mathbb{Q}(u)$. It concerns a candidate, so it is vacuous if Diaz's conjecture holds. Not found in the sources read.
-- source:
--   The candidate case of the transcendence-degree-one form of Diaz's conjecture (Qr2) (G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, pp. 376–377, the reading ℝℓ ∩ ℒ = ℚℓ, iℝℓ ∩ ℒ = {0} at ℓ = ū), through `DiazModulus.log_mul_real_trichotomy_of_trdeg_one` and `DiazModulus.log_mul_imaginary_mixed_of_trdeg_one`. Not found in the sources read. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem candidate_log_mul_real_iff_rat_conj (u : ℂ) (hu : IsCandidate u) (μ : ℂ) (hμ : μ ≠ 0)
    (heμ : IsAlgebraic ℚ (Complex.exp μ))
    (hμu : IsAlgebraic (↥(Algebra.adjoin ℚ ({u} : Set ℂ))) μ) :
    ((u * μ).im = 0 ↔ ∃ q : ℚ, μ = (q : ℂ) * conj u) ∧ (u * μ).re ≠ 0 := by
  sorry

end DiazModulus
