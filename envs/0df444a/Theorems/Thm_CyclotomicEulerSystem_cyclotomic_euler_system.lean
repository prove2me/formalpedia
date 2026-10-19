-- Prove2me | Theorems.Thm_CyclotomicEulerSystem_cyclotomic_euler_system
-- name    : CyclotomicEulerSystem.cyclotomic_euler_system
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T15:29:38.258812+00:00
-- url     : https://prove2.me/theorems/ec818412-96c6-4dce-be12-078b3839c5dc
-- title:
--   Cyclotomic Euler system relations
-- statement:
--   Throughout, $\zeta = (\zeta_n)$ is a **compatible system of roots of unity** in $\mathbb C$: for every square-free positive integer $n$, $\zeta_n$ is a primitive $n$-th root of unity, and $\zeta_{mn} = \zeta_m\zeta_n$ whenever $m,n$ are coprime square-free positive integers. Write $\alpha_n = 1-\zeta_n$ and $\mathbb Q(\zeta_n)\subseteq\mathbb C$ for the $n$-th cyclotomic field.
--
--   Let $n$ be square-free and $l$ a prime with $l\nmid n$. Then the cyclotomic units satisfy the two Euler-system relations:
--
--   1. (**Norm relation**) If $n>1$ and $\mathrm{Fr}_l$ is the automorphism of $\mathbb Q(\zeta_n)/\mathbb Q$ with $\mathrm{Fr}_l(\zeta_n)=\zeta_n^{\,l}$, then
--   $$N_{\mathbb Q(\zeta_{nl})/\mathbb Q(\zeta_n)}(\alpha_{nl})=\alpha_n^{\mathrm{Fr}_l-1}=\frac{\mathrm{Fr}_l(\alpha_n)}{\alpha_n}.$$
--   2. (**Congruence relation**) For every prime ideal $\mathfrak P$ of the ring of integers of $\mathbb Q(\zeta_{nl})$ lying above $l$,
--   $$\alpha_{nl}\equiv\alpha_n\pmod{\mathfrak P}.$$
--
--   These two relations are what make $(\alpha_n)_n$ an Euler system; they are the input to Kolyvagin's and Rubin's Euler-system arguments bounding ideal class groups.
--
--   **Formalization Note** The base field of the norm is $\mathbb Q(\zeta_n)$ (the source's $\mathbb Q(\zeta_l)$ is a typo), and $n>1$ is required in the norm relation because $\alpha_1=0$. See the two milestone statements for the encoding details.
-- source:
--   Wikipedia, "Euler system", revision 1353502478 (https://en.wikipedia.org/w/index.php?title=Euler_system&oldid=1353502478), section "Examples / Cyclotomic units", displayed relations (norm relation and congruence relation) and the preceding sentence "For every square-free positive integer n pick an n-th root ζ_n of 1, with ζ_mn = ζ_m ζ_n for m,n coprime. Then the cyclotomic Euler system is the set of numbers α_n = 1 − ζ_n."

import Mathlib
import Definitions.Def_CyclotomicEulerSystem_defs

open NumberField

namespace CyclotomicEulerSystem

theorem cyclotomic_euler_system (ζ : ℕ → ℂ) (hζ : IsCompatibleRootSystem ζ) (n l : ℕ)
    (hn : Squarefree n) (hl : l.Prime) (hln : ¬ l ∣ n) :
    (1 < n → ∀ Frob : cycField ζ n ≃ₐ[ℚ] cycField ζ n, Frob (zetaIn ζ n) = zetaIn ζ n ^ l →
      ((Algebra.norm (cycField ζ n) (alphaExt ζ n (n * l)) : cycField ζ n) : ℂ) =
        (Frob (alphaIn ζ n) : ℂ) / alpha ζ n) ∧
    (∀ P : Ideal (𝓞 (cycField ζ (n * l))), P.IsPrime →
      (l : 𝓞 (cycField ζ (n * l))) ∈ P →
      ∀ x y : 𝓞 (cycField ζ (n * l)),
        ((x : cycField ζ (n * l)) : ℂ) = alpha ζ (n * l) →
        ((y : cycField ζ (n * l)) : ℂ) = alpha ζ n → x - y ∈ P) := by sorry

end CyclotomicEulerSystem
