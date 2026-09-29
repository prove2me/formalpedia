-- Prove2me | Theorems.Thm_Deformation_DieudonneModule_exists_mvPowerSeries_coeff_eq_apply_of_forall_map_eq
-- name    : Deformation.DieudonneModule.exists_mvPowerSeries_coeff_eq_apply_of_forall_map_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/77054ccc-13db-5f81-9099-9a634bd31922
-- title:
--   Covector coordinates of a compatible Dieudonné family
-- statement:
--   Fix a prime $p$ and $d\in\mathbb N$, and let $H:\mathbb N\to\mathrm{Type}$ be a family of commutative rings, each a bialgebra over $\mathbb Z/p$, together with bialgebra homomorphisms $s_v\colon H(v+1)\to H(v)$. Suppose given $(\mathbb Z/p)$-algebra homomorphisms $\pi_v\colon (\mathbb Z/p)[[X_0,\dots,X_{d-1}]]\to H(v)$ (formal power series in $\mathrm{Fin}\,d$ variables) such that $\pi_{v+1}$ followed by $s_v$ equals $\pi_v$; the counit of $\pi_v(X_i)$ vanishes for all $v,i$; a power series $G$ with $\pi_v G=0$ for all $v$ is zero; every family $z_v\in H(v)$ with $s_v(z_{v+1})=z_v$ is of the form $z_v=\pi_v G$ for some $G$; and for every $N$ there is a $v$ with $\ker \pi_v\subseteq I^N$, where $I=(X_0,\dots,X_{d-1})$. Let $m_v$ be elements of the Dieudonné modules $\varinjlim_n \mathrm{wittHom}(\mathbb Z/p,p,n,H(v))$ — the colimit along shift maps of the groups of $x\in \mathrm{TruncatedWittVector}\,p\,n\,H(v)$ whose image under the comultiplication equals the sum of its images under the two inclusions $H(v)\to H(v)\otimes H(v)$ — compatible in the sense that $\mathrm{map}(s_v)(m_{v+1})=m_v$. Then there is a sequence $\bar a_k$ of power series with zero constant term, tending to $0$ $I$-adically (for each $N$ some $k_0$ with $\bar a_k\in I^N$ for all $k\ge k_0$), such that for all $v,n$, every $u$ in the $n$-th group whose image in the colimit is $m_v$, and every $k<n$, the $(n-1-k)$-th Witt coordinate of $u$ equals $\pi_v(\bar a_k)$; and any sequence satisfying this last coordinate identity coincides with $\bar a$.
--
--   This is the explicit form of Fontaine's identification of the contravariant Dieudonné module of a formal group with a group of Witt covectors over its affine algebra: a compatible family $m=(m_v)$ "is" the covector $(\dots,\bar a_2,\bar a_1,\bar a_0)$ written in the formal coordinates $X_0,\dots,X_{d-1}$, with $k=0$ indexing the last Witt coordinate. It is used in the construction of normal-form coefficients for bases of multidimensional formal groups, via [`Deformation.HondaSystem.exists_mvFormalGroup_basis_coeff_eq_normalForm`](thm.html#Deformation.HondaSystem.exists_mvFormalGroup_basis_coeff_eq_normalForm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_DieudonneModule_exists_mvPowerSeries_coeff_eq_apply_of_forall_map_eq.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe v

theorem Deformation.DieudonneModule.exists_mvPowerSeries_coeff_eq_apply_of_forall_map_eq
    (p : ℕ) [Fact p.Prime] {d : ℕ}
    (H : ℕ → Type v) [∀ v, CommRing (H v)] [∀ v, Bialgebra (ZMod p) (H v)]
    (s : ∀ v, H (v + 1) →ₐc[ZMod p] H v)
    (π : ∀ v, MvPowerSeries (Fin d) (ZMod p) →ₐ[ZMod p] H v)
    (hπs : ∀ v, (s v : H (v + 1) →ₐ[ZMod p] H v).comp (π (v + 1)) = π v)
    (hπε : ∀ v i, Coalgebra.counit (R := ZMod p) (π v (MvPowerSeries.X i)) = 0)
    (hπinj : ∀ G : MvPowerSeries (Fin d) (ZMod p), (∀ v, π v G = 0) → G = 0)
    (hπsurjj : ∀ z : ∀ v, H v, (∀ v, s v (z (v + 1)) = z v) →
      ∃ G : MvPowerSeries (Fin d) (ZMod p), ∀ v, π v G = z v)
    (hπker : ∀ N : ℕ, ∃ v, RingHom.ker (π v) ≤
      (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N)
    (m : ∀ v, Deformation.DieudonneModule (ZMod p) p (H v))
    (hm : ∀ v, Deformation.DieudonneModule.map (ZMod p) p (s v) (m (v + 1)) = m v) :
    ∃ abar : ℕ → MvPowerSeries (Fin d) (ZMod p),
      (∀ k, MvPowerSeries.constantCoeff (abar k) = 0) ∧
      (∀ N : ℕ, ∃ k₀, ∀ k, k₀ ≤ k →
        abar k ∈ (Ideal.span (Set.range (MvPowerSeries.X : Fin d → MvPowerSeries (Fin d) (ZMod p)))) ^ N) ∧
      (∀ (v n : ℕ) (u : Deformation.wittHom (ZMod p) p n (H v)),
        Deformation.DieudonneModule.of (ZMod p) p (H v) n u = m v →
        ∀ (k : ℕ) (hk : k < n),
          (u : TruncatedWittVector p n (H v)).coeff ⟨n - 1 - k, by omega⟩ = π v (abar k)) ∧
      (∀ abar' : ℕ → MvPowerSeries (Fin d) (ZMod p),
        (∀ (v n : ℕ) (u : Deformation.wittHom (ZMod p) p n (H v)),
          Deformation.DieudonneModule.of (ZMod p) p (H v) n u = m v →
          ∀ (k : ℕ) (hk : k < n),
            (u : TruncatedWittVector p n (H v)).coeff ⟨n - 1 - k, by omega⟩ = π v (abar' k)) →
        abar' = abar) := by sorry
