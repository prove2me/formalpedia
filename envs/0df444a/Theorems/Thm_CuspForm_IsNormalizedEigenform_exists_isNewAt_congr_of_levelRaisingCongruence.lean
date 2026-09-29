-- Prove2me | Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_isNewAt_congr_of_levelRaisingCongruence
-- name    : CuspForm.IsNormalizedEigenform.exists_isNewAt_congr_of_levelRaisingCongruence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/1d6e0a6e-f477-569a-9c93-b07582baa397
-- title:
--   Level raising at q' for weight-two normalised eigenforms
-- statement:
--   Let $N$ be a positive integer, let $p$ be a prime with $p \neq 2$, and let $q'$ be a prime with $q' \nmid N$ and $q' \neq p$. Let $f$ be a weight-two cusp form on $\Gamma_0(N)$ which is a normalised eigenform in the sense recorded by `IsNormalizedEigenform`: writing $a_n(f)$ for the $n$-th coefficient of the $q$-expansion of $f$ at width $1$, one has $a_1(f)=1$, $a_{mn}(f)=a_m(f)a_n(f)$ for coprime $m,n$, $a_{r^{k+2}}(f)=a_r(f)a_{r^{k+1}}(f)-r\,a_{r^k}(f)$ for primes $r \nmid N$, and $a_{r^{k+2}}(f)=a_r(f)a_{r^{k+1}}(f)$ for primes $r \mid N$. Let $\mathfrak m$ be a maximal ideal of the ring $\overline{\mathbf Z}$ of algebraic integers in $\mathbf C$ (the integral closure of $\mathbf Z$ in $\mathbf C$) with $p \in \mathfrak m$. Assume: (i) there is a prime $\ell$ with $\ell \nmid N$, $\ell \neq p$, $\ell \neq q'$, such that every $a \in \overline{\mathbf Z}$ whose image in $\mathbf C$ is $a_\ell(f)$ satisfies $a - (\ell + 1) \notin \mathfrak m$; and (ii) there is $a \in \overline{\mathbf Z}$ with image $a_{q'}(f)$ in $\mathbf C$ and $a^2 - (q'+1)^2 \in \mathfrak m$. Then there exists a weight-two cusp form $g$ on $\Gamma_0(Nq')$ which is a normalised eigenform in the same sense, satisfies $a_{q'}(g)^2 = 1$, and is such that for every prime $\ell$ with $\ell \nmid Nq'$ and $\ell \neq p$ there are $a, b \in \overline{\mathbf Z}$ with images $a_\ell(f)$ and $a_\ell(g)$ in $\mathbf C$ and $a - b \in \mathfrak m$.
--
--   This is Ribet's level-raising theorem in the form used on the Frey-curve side: a weight-two eigenform of level $N$ whose $q'$-th coefficient satisfies $a_{q'}^2 \equiv (q'+1)^2$ modulo a non-Eisenstein maximal ideal $\mathfrak m$ above $p$ admits a companion eigenform of level $Nq'$, new at $q'$ in the sense $a_{q'}(g)^2 = 1$, congruent to it modulo $\mathfrak m$ at all primes away from $Nq'p$. It is the eigenform-level input to [`WeierstrassCurve.exists_newAt_congruentEigenform_of_levelRaisingCongruence`](thm.html#WeierstrassCurve.exists_newAt_congruentEigenform_of_levelRaisingCongruence).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNormalizedEigenform_exists_isNewAt_congr_of_levelRaisingCongruence.lean

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FreyPackage_LevelRaising

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped CongruenceSubgroup

theorem CuspForm.IsNormalizedEigenform.exists_isNewAt_congr_of_levelRaisingCongruence
    {N : ℕ} (hN : 0 < N) {p q' : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) (hq'p : q' ≠ p)
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) (hmax : 𝔪.IsMaximal)
    (hpm : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (hne : ∃ ℓ : ℕ, ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ≠ p ∧ ℓ ≠ q' ∧
      ∀ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ →
        a - ((ℓ : integralClosure ℤ ℂ) + 1) ∉ 𝔪)
    (hLR : ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f q' ∧
      a ^ 2 - ((q' : integralClosure ℤ ℂ) + 1) ^ 2 ∈ 𝔪) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 (N * q')) 2,
      g.IsNormalizedEigenform ∧ g.IsNewAt q' ∧
      ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * q' → ℓ ≠ p →
        ∃ a b : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
          (b : ℂ) = ModularFormClass.qCoeff g ℓ ∧ a - b ∈ 𝔪 := by sorry
