-- Prove2me | Theorems.Thm_DiazModulus_iteratedDeriv_iteratedFDeriv_line
-- name    : DiazModulus.iteratedDeriv_iteratedFDeriv_line
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:05:30.246982+00:00
-- url     : https://prove2.me/theorems/1795bb3b-5045-45c2-85f0-bd8a8edd03de
-- title:
--   For entire $f$ on $\mathbb{C}^n$, the $q$-th derivative at $0$ of $z \mapsto D^\sigma f(z\zeta)(v)$ is $D^{\sigma+q} f(0)$ at $v$ followed by $q$ copies of $\zeta$
-- statement:
--   Let $f$ be an entire function on $\mathbb{C}^n$, $\zeta \in \mathbb{C}^n$, $\sigma, q \in \mathbb{N}$ and $v_1, \dots, v_\sigma \in \mathbb{C}^n$. Then the $q$-th derivative at $z = 0$ of $z \mapsto D^\sigma f(z\zeta)(v_1, \dots, v_\sigma)$ is $D^{\sigma + q} f(0)(v_1, \dots, v_\sigma, \zeta, \dots, \zeta)$, with $q$ copies of $\zeta$.
--
--   **Proof.** The identity holds at every $z$. For one derivative, the chain rule for $z \mapsto z\zeta$, whose derivative is $\zeta$, gives $D^{N+1} f(z\zeta)(\zeta, w)$, since evaluation at a fixed tuple is a continuous linear map. Induction on $q$ puts each further $\zeta$ in front of the arguments, while the statement has it at the end; the two agree by the symmetry of iterated derivatives of a smooth function.
--
--   **Novelty.** Classical; routine formalisation. The chain rule along a line, used in the proof of DALAG Lemma 9.2.
-- source:
--   Classical (chain rule and symmetry of derivatives). Used for M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Lemma 9.2. C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem iteratedDeriv_iteratedFDeriv_line {n : ℕ} (f : (Fin n → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (ζ : Fin n → ℂ) (σ q : ℕ) (v : Fin σ → Fin n → ℂ) :
    iteratedDeriv q (fun z : ℂ => iteratedFDeriv ℂ σ f (z • ζ) v) 0 =
      iteratedFDeriv ℂ (σ + q) f 0 (Fin.append v (fun _ : Fin q => ζ)) := by
  sorry

end DiazModulus
