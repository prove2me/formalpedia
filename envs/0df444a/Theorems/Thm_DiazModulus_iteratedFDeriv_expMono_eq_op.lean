-- Prove2me | Theorems.Thm_DiazModulus_iteratedFDeriv_expMono_eq_op
-- name    : DiazModulus.iteratedFDeriv_expMono_eq_op
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-29T06:05:37.551945+00:00
-- url     : https://prove2.me/theorems/ce3bf9db-7b3c-4b45-b64f-04682aa0512a
-- title:
--   $\partial_{w_1} \cdots \partial_{w_r} (z'^\tau e^{\langle t, z''\rangle})$ is $\mathrm{Op}_{w_1} \cdots \mathrm{Op}_{w_r} X^\tau$ times the exponential, for the operators Op of DALAG's derivations
-- statement:
--   Points are $p = (p', p'') \in \mathbb{C}^{\iota_0} \times \mathbb{C}^{\iota_1}$ for finite index sets $\iota_0, \iota_1$. For $w = (w', w'')$ and a weight vector $t$ on $\iota_1$, $\mathrm{Op}^t_w$ is the operator $\sum_{h \in \iota_0} w'_h\,\partial/\partial X_h + \sum_{i \in \iota_1} w''_i t_i$ on polynomials in the $X_h$ ($h \in \iota_0$), and for vectors $w_k$ ($k \in \kappa_0$) and $k_1, \dots, k_r \in \kappa_0$, $\mathrm{Op}^t_{w,k} = \mathrm{Op}^t_{w_{k_1}} \cdots \mathrm{Op}^t_{w_{k_r}}$ (the factors commute). Let $\tau \in \mathbb{N}^{\iota_0}$, $t \in \mathbb{Z}^{\iota_1}$, $p$ a point, and $f(z) = z'^\tau e^{\langle t, z'' \rangle}$, where $z'^\tau = \prod_h z_h'^{\tau_h}$ and $\langle t, z'' \rangle = \sum_i t_i z''_i$. Then for $k_1, \dots, k_r \in \kappa_0$, $D^r f(p)(w_{k_1}, \dots, w_{k_r}) = (\mathrm{Op}^t_{w,k} X^\tau)(p')\, e^{\langle t, p'' \rangle}$.
--
--   **Proof.** For a polynomial $Q$ put $G_Q(z) = Q(z') e^{\langle t, z'' \rangle}$. The product rule and the derivative of polynomial evaluation (by induction on $Q$) give $DG_Q(z)\,v = G_{\mathrm{Op}^t_v Q}(z)$. Then induct on $r$ for all $Q$ at once: the $(r+1)$-st derivative is the $r$-th derivative of $DG_Q$ evaluated at the last direction, and evaluation at a fixed vector commutes with iterated derivatives, which gives the $r$-th derivative of $G_{\mathrm{Op}^t_{w_{k_{r+1}}} Q}$. Take $Q = X^\tau$.
--
--   **Novelty.** Classical; routine formalisation. It is the action of the derivations $D_w$ of DALAG on $X^\tau Y^t$, read through the exponential map, as in Step 3 of the proof of DALAG Th. 11.21.
-- source:
--   Classical; the invariant derivations D_w of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, §8.1 and §8.3.2 (Lemma 8.11), as used in Step 3 of the proof of Th. 11.21 (§11.7.1). C1.4 of the Diaz modulus mission. Formal proof: Diaz modulus mission, 29 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem iteratedFDeriv_expMono_eq_op {ι₀ ι₁ κ₀ : Type} [Fintype ι₀] [Fintype ι₁] [DecidableEq ι₀]
    (w : κ₀ → (ι₀ → ℂ) × (ι₁ → ℂ)) (τ : ι₀ → ℕ) (t : ι₁ → ℤ) (p : (ι₀ → ℂ) × (ι₁ → ℂ))
    (r : ℕ) (κ : Fin r → κ₀) :
    iteratedFDeriv ℂ r (fun z : (ι₀ → ℂ) × (ι₁ → ℂ) =>
        (∏ h, z.1 h ^ τ h) * Complex.exp (∑ i, (t i : ℂ) * z.2 i)) p (fun k => w (κ k)) =
      MvPolynomial.eval p.1 ((List.ofFn fun k : Fin r =>
            ((∑ h, (w (κ k)).1 h • (MvPolynomial.pderiv h).toLinearMap
              + (∑ i, (w (κ k)).2 i * (t i : ℂ)) • LinearMap.id :
                Module.End ℂ (MvPolynomial ι₀ ℂ)))).prod
          (∏ h, MvPolynomial.X h ^ τ h)) * Complex.exp (∑ i, (t i : ℂ) * p.2 i) := by
  sorry

end DiazModulus
