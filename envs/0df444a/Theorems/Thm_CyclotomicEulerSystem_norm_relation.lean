-- Prove2me | Theorems.Thm_CyclotomicEulerSystem_norm_relation
-- name    : CyclotomicEulerSystem.norm_relation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T15:28:00.942865+00:00
-- url     : https://prove2.me/theorems/1a4e266c-1d27-4be8-9a51-fadb6f9f4234
-- title:
--   Norm relation $N_{\mathbb Q(\zeta_{nl})/\mathbb Q(\zeta_n)}(\alpha_{nl})=\alpha_n^{\mathrm{Fr}_l-1}$
-- statement:
--   Throughout, $\zeta = (\zeta_n)$ is a **compatible system of roots of unity** in $\mathbb C$: for every square-free positive integer $n$, $\zeta_n$ is a primitive $n$-th root of unity, and $\zeta_{mn} = \zeta_m\zeta_n$ whenever $m,n$ are coprime square-free positive integers. Write $\alpha_n = 1-\zeta_n$ and $\mathbb Q(\zeta_n)\subseteq\mathbb C$ for the $n$-th cyclotomic field.
--
--   Let $n>1$ be square-free, let $l$ be a prime with $l\nmid n$, and let $\mathrm{Fr}_l$ be the Frobenius automorphism of $\mathbb Q(\zeta_n)/\mathbb Q$, i.e. the field automorphism with $\mathrm{Fr}_l(\zeta_n)=\zeta_n^{\,l}$. Then
--   $$N_{\mathbb Q(\zeta_{nl})/\mathbb Q(\zeta_n)}(\alpha_{nl}) \;=\; \alpha_n^{\mathrm{Fr}_l-1} \;=\; \frac{\mathrm{Fr}_l(\alpha_n)}{\alpha_n}.$$
--
--   This is the Euler-system norm relation for cyclotomic units: going down one prime level multiplies by the Euler factor $\mathrm{Fr}_l-1$ (written multiplicatively).
--
--   **Formalization Note** (1) The source prints the norm as $N_{\mathbb Q(\zeta_{nl})/\mathbb Q(\zeta_l)}$; this is a typo, since $\alpha_n^{\mathrm{Fr}_l-1}$ lies in $\mathbb Q(\zeta_n)$ and $\mathrm{Fr}_l$ acts on $\zeta_n$; the base field is $\mathbb Q(\zeta_n)$, as in the standard references (e.g. Rubin, *Euler Systems*). (2) The hypothesis $n>1$ is added: for $n=1$, $\zeta_1=1$ and $\alpha_1=0$, so the right-hand side is undefined, while the left-hand side is $N_{\mathbb Q(\zeta_l)/\mathbb Q}(1-\zeta_l)=l$. (3) The extension $\mathbb Q(\zeta_{nl})/\mathbb Q(\zeta_n)$ is encoded as $\mathbb Q(\zeta_n)(\zeta_{nl})$ inside $\mathbb C$, and the norm is `Algebra.norm`; the multiplicative exponent $\alpha^{\mathrm{Fr}_l-1}$ is written as the quotient $\mathrm{Fr}_l(\alpha_n)/\alpha_n$ in $\mathbb C$. The statement is made for every automorphism $\mathrm{Fr}_l$ of $\mathbb Q(\zeta_n)$ over $\mathbb Q$ sending $\zeta_n$ to $\zeta_n^l$ (there is exactly one).
-- source:
--   Wikipedia, "Euler system", revision 1353502478 (https://en.wikipedia.org/w/index.php?title=Euler_system&oldid=1353502478), section "Examples / Cyclotomic units", displayed relations (norm relation and congruence relation) and the preceding sentence "For every square-free positive integer n pick an n-th root ζ_n of 1, with ζ_mn = ζ_m ζ_n for m,n coprime. Then the cyclotomic Euler system is the set of numbers α_n = 1 − ζ_n."

import Mathlib
import Definitions.Def_CyclotomicEulerSystem_defs

open NumberField

namespace CyclotomicEulerSystem

theorem norm_relation (ζ : ℕ → ℂ) (hζ : IsCompatibleRootSystem ζ) (n l : ℕ)
    (hn : Squarefree n) (hn1 : 1 < n) (hl : l.Prime) (hln : ¬ l ∣ n)
    (Frob : cycField ζ n ≃ₐ[ℚ] cycField ζ n) (hFrob : Frob (zetaIn ζ n) = zetaIn ζ n ^ l) :
    ((Algebra.norm (cycField ζ n) (alphaExt ζ n (n * l)) : cycField ζ n) : ℂ) =
      (Frob (alphaIn ζ n) : ℂ) / alpha ζ n := by sorry

end CyclotomicEulerSystem
